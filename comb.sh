#!/bin/sh

# Perform affine reductions eagerly instead of call-by-name
OPT=y

INDENT=

err() {
    echo Error: $* >&2
    exit 1
}

# binary expressions
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
pair()
{
    if [ $# -ne 2 ]; then
        err pair
    fi
    echo "( $1 ) $2"
}
app()
{
    if [ $# -ne 2 ]; then
        err app
    fi
    simplify $(pair "$1" "$2")
}
app3()
{
    if [ $# -ne 3 ]; then
        err app3
    fi
    lhs=$(app "$1" "$2")
    app "$lhs" "$3"
}
app4()
{
    if [ $# -ne 4 ]; then
        err app4
    fi
    lhs=$(app3 "$1" "$2" "$3")
    app "$lhs" "$4"
}

# free variables
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
        app k "$*"
        return
    fi

    split $*
    # Turner-style translation
    if free $x $left; then
        if free $x $right; then
            app3 s "$(lam $x $left)" "$(lam $x $right)"
        else
            # f: flip
            app3 f "$(lam $x $left)" "$right"
        fi
    else
        if free $x $right; then
            # c: compose
            app3 c "$left" "$(lam $x $right)"
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
        prog=$(pair "$prog" "$left")
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

# in safe mode, don't do possibly nonterminating reductions or i/o,
# and don't print anything
SAFE=
unsafe() {
    if [ z$SAFE != z ]; then
        return 1
    fi
}

# the evaluator itself
# combinators:
#   s, k, i,
#   c -- composition,
#   f -- flip,
#   echo x -- print term x
#   read -- read term x
#   toch -- turn a shell number into a church numeral
#   succ -- increment a shell number
reduce1() {
    context=end
    prog="$*"

    while true; do
        case "$prog" in
        "("*)
            split $prog
            prog="$left"
            context=$(pair "$right" "$context")
            ;;
        *)
            break
            ;;
        esac
    done

    case "$prog" in
    echo)
        (unsafe && args 1) || return 1
        split $context
        echo The answer is: $(force $left) >&2
        echo $(repack "$right" i)
        ;;
    read)
        (unsafe && args 1) || return 1
        read -p "Enter a number: " i
        split $context
        k=$(app "$left" $i)
        echo $(repack "$right" "$k")
        ;;
    toch)
        (unsafe && args 1) || return 1
        split $context
        i=$(force $left)
        num=Z
        for _ in $(seq 1 $i); do
            num=$(app S "$num")
        done
        num=$(lam S $(lam Z $num))
        echo $(repack "$right" "$num")
        ;;
    succ)
        (unsafe && args 1) || return 1
        split $context
        x=$(($(force $left)+1))
        echo $(repack "$right" $x)
        ;;
    s)
        (unsafe && args 3) || return 1
        split $context
        x=$left
        split $right
        y=$left
        split $right
        z=$left
        a=$(app "$x" "$z")
        b=$(app "$y" "$z")
        c=$(app "$a" "$b")
        echo $(repack "$right" "$c")
        ;;
    f)
        args 3 || return 1
        split $context
        x=$left
        split $right
        y=$left
        split $right
        z=$left
        r=$(app3 "$x" "$z" "$y")
        echo $(repack "$right" "$r")
        ;;
    c)
        args 3 || return 1
        split $context
        x=$left
        split $right
        y=$left
        split $right
        z=$left
        yz=$(app "$y" "$z")
        r=$(app "$x" "$yz")
        echo $(repack "$right" "$r")
        ;;
    k)
        args 2 || return 1
        split $context
        x=$left
        split $right
        y=$left
        echo $(repack "$right" "$x")
        ;;
    i)
        args 1 || return 1
        split $context
        echo $(repack "$right" "$left")
        ;;
    *)
        return 1
        ;;
    esac
}

reduce() {
    prog=$*
    arrow="  "

    echo >&2
    while [ "$prog" != stuck ]; do
        echo "$INDENT$arrow $prog" >&2
        arrow="->"
        oldprog=$prog
        prog=$(reduce1 $prog || echo stuck)
    done

    echo $oldprog
}

if [ z$OPT = zy ]; then
simplify() {
    OLD_SAFE=$SAFE
    export SAFE=yes
    reduce1 $* || echo $*
    export SAFE=$OLD_SAFE
}
else
simplify() {
    echo $*
}
fi
force() {
    OLD_INDENT=$INDENT
    INDENT="$INDENT  "
    reduce $*
    INDENT=$OLD_INDENT
}

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
unsafe || echo oops

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
