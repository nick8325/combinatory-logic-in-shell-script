#!/bin/sh

# if y, perform certain affine reductions eagerly
# (might make things slower)
EAGER=y

INDENT=

err() {
    echo Error: $* >&2
    exit 1
}

# pairs/function application.
# we encode t u as ( t ) u.
split_()
{
    if [ z$1 != "z(" ]; then
        return 1
    fi
    left=
    stack=1
    shift
    while [ $stack -ne 0 ] ; do
        case $1 in
        "(" ) stack=$(($stack+1)) ;;
        ")" ) stack=$(($stack-1)) ;;
        esac
        if [ $stack -ne 0 ]; then
            left="$left $1"
        fi
        shift
    done
    left=$(echo $left)
    export left
    export right="$*"
}
split()
{
    split_ $(echo $*)
}
# apply a function to an argument
pack()
{
    if [ $# -ne 2 ]; then
        err pack
    fi
    echo "( $1 ) $2"
}
pack3()
{
    if [ $# -ne 3 ]; then
        err pack3
    fi
    lhs=$(pack "$1" "$2")
    pack "$lhs" "$3"
}
pack4()
{
    if [ $# -ne 4 ]; then
        err pack4
    fi
    lhs=$(pack3 "$1" "$2" "$3")
    pack "$lhs" "$4"
}

# apply a function to an argument and reduce to WHNF
# or until the head is a non-affine combinator
app() {
    simplify $(pack "$@")
}
app3() {
    simplify $(pack3 "$@")
}
app4() {
    simplify $(pack4 "$@")
}

# free x t: is x free in t?
free_() {
    x=$1
    shift
    for i in $*; do
        if [ $x = $i ]; then
            return 0
        fi
    done
    return 1
}
free() {
    free_ $(echo $*)
}

# lambda abstraction
lam_() {
    x=$1
    shift

    if [ "$*" = $x ]; then
        echo "i"
        return
    fi

    if ! free $x $*; then
        pack k "$*"
        return
    fi

    split $*
    # Turner-style translation
    if free $x $left; then
        if free $x $right; then
            pack3 s "$(lam $x $left)" "$(lam $x $right)"
        else
            # f: flip
            pack3 f "$(lam $x $left)" "$right"
        fi
    else
        if free $x $right; then
            if [ $x = "$right" ]; then
                # eta-reduce
                echo "$left"
            else
                # c: compose
                pack3 c "$left" "$(lam $x $right)"
            fi
        else
            err lam
        fi
    fi
}
lam() {
    lam_ $(echo $*)
}

#
# an evaluator
#

# the evaluation function works with a (term, context)
# pair---a context is a stack of terms.
# evaluation of t u pushes u onto the context and
# evaluates t.

# combine a term and a context
repack() {
    stack=$1
    prog=$2

    while [ "$stack" != end ]; do
        split $stack
        prog=$(pack "$prog" "$left")
        stack=$right
    done
    echo $prog
}

# terminate if a combinator is undersaturated
args() {
    right=$context
    for _ in $(seq 1 $1); do
        if ! split $right; then
            return 1
        fi
    done
}

# in safe mode, don't do possibly nonterminating reductions or i/o.
# (safe mode is used to simplify terms when EAGER=y)
SAFE=
unsafe() {
    if [ z$SAFE != z ]; then
        return 1
    fi
}

# the evaluator itself
# environment variables:
#   prog -- the current term
#   context -- the context
# both are modified by reduction
# combinators:
#   s, k, i,
#   c -- composition,
#   f -- flip,
#   echo x -- print term x
#   read -- read term x
#   toch -- turn a shell number into a church numeral
#   succ -- increment a shell number
reduce1() {
    while true; do
        case "$prog" in
        "("*)
            split $prog
            prog="$left"
            context=$(pack "$right" "$context")
            ;;
        *)
            break
            ;;
        esac
    done

    export prog context

    case "$prog" in
    echo)
        (unsafe && args 1) || return 1
        split $context
        echo The answer is: $(force $left) >&2
        prog=i
        context=$right
        ;;
    read)
        (unsafe && args 1) || return 1
        read -p "Enter a number: " i
        split $context
        prog=$(pack "$left" $i)
        context=$right
        ;;
    toch)
        (unsafe && args 1) || return 1
        split $context
        i=$(force $left)
        num=Z
        for _ in $(seq 1 $i); do
            num=$(pack S "$num")
        done
        prog=$(lam S $(lam Z $num))
        context=$right
        ;;
    succ)
        (unsafe && args 1) || return 1
        split $context
        prog=$(($(force $left)+1))
        context=$right
        ;;
    s)
        (unsafe && args 3) || return 1
        split $context
        x=$left
        split $right
        y=$left
        split $right
        z=$(simplify $left)
        yz=$(pack "$y" "$z")
        prog=$(pack3 "$x" "$z" "$yz")
        context=$right
        ;;
    f)
        args 3 || return 1
        split $context
        x=$left
        split $right
        y=$left
        split $right
        z=$left
        prog=$(pack3 "$x" "$z" "$y")
        context=$right
        ;;
    c)
        args 3 || return 1
        split $context
        x=$left
        split $right
        y=$left
        split $right
        z=$left
        yz=$(pack "$y" "$z")
        prog=$(pack "$x" "$yz")
        context=$right
        ;;
    k)
        args 2 || return 1
        split $context
        x=$left
        split $right
        y=$left
        prog=$x
        context=$right
        ;;
    i)
        args 1 || return 1
        split $context
        prog=$left
        context=$right
        ;;
    *)
        return 1
        ;;
    esac

    export prog context
}

reduce() {
    prog=$*
    context=end

    echo >&2
    echo "$INDENT   $prog" >&2
    while reduce1; do
        prog_=$(repack "$context" "$prog")
        echo >&2
        echo "$INDENT-> $prog_" >&2
    done

    repack "$context" "$prog"
}

force() {
    INDENT="$INDENT  "
    reduce $*
}

if [ z$EAGER = zy ]; then
simplify() {
    SAFE=y
    prog=$*
    context=end

    if reduce1; then
        while reduce1; do
            true
        done

        repack "$context" "$prog"
    else
        echo $*
    fi
}
else
simplify() {
    echo $*
}
fi

# y combinator
y_=$(lam X $(app F "$(app X X)"))
y=$(lam F $(app "$y_" "$y_"))

# church numerals
z=$(lam S $(lam Z Z))
s=$(lam N $(lam S $(lam Z $(app S "$(app3 N S Z)"))))
isz=$(lam N $(lam T $(lam F $(app3 N "$(lam _ F)" T))))
plus=$(lam M $(lam N $(app3 M "$s" N)))

# conversion & i/o of church numerals
fromch=$(lam N $(app3 N succ 0))
print=$(lam N $(app echo "$(app3 N succ 0)"))
input_=$(lam N $(app K "$(app toch N)"))
input=$(lam K $(app read "$input_"))

# this program reads in numbers until you type in 0.
# then it prints their sum.
# beware! it is very slow! :)

done=$(app "$print" Acc)
acc_=$(app3 "$plus" Acc N)
again=$(app Loop "$acc_")
body=$(app4 "$isz" N "$done" "$again")
loop_=$(app "$input" "$(lam N $body)")
loop=$(app "$y" "$(lam Loop $(lam Acc $loop_))")

reduce $(app "$loop" "$z")
