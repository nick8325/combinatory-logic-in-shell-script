#!/bin/sh

set -e

# if y, perform certain affine reductions eagerly and silently
# (might make things slower)
EAGER=y

# if y, print out reductions as you go
TRACE=y

INDENT=

err() {
    echo Error: $* >&2
    exit 1
}

# encoding of pairs/function application.
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
app()
{
    if [ $# -ne 2 ]; then
        err app
    fi
    echo "( $1 ) $2"
}
app3()
{
    if [ $# -ne 3 ]; then
        err app3
    fi
    lhs=$(app "$1" "$2")
    app "$lhs" "$3"
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
        prog=$(app "$prog" "$left")
        stack=$right
    done
    echo $prog
}

# terminate if a combinator is undersaturated
args() {
    right=$context
    for xxx in $(seq 1 $1); do
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

# the evaluator itself.
# environment variables:
#   prog -- the current term
#   context -- the context
# both are modified by reduction.
# combinators:
#   s, k, i,
#   c -- composition,
#   f -- flip,
#   echo x -- print term x
#   read -- read term x
#   toch -- turn a shell number into a church numeral
#   succ -- increment a shell number
#   force x k -- reduce x and then evaluate k x
reduce1() {
    while true; do
        case "$prog" in
        "("*)
            split $prog
            prog="$left"
            context=$(app "$right" "$context")
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
        unsafe || return 1
        echo -n "Enter a term: " >&2
        read i
        prog="$(compile $i)"
        ;;
    toch)
        (unsafe && args 1) || return 1
        split $context
        i=$(force $left)
        prog=$(app k i)
        for xxx in $(seq 1 $i); do
            prog=$(app "$(app s c)" "$prog")
        done
        context=$right
        ;;
    succ)
        (unsafe && args 1) || return 1
        split $context
        prog=$(($(force $left)+1))
        context=$right
        ;;
    force)
        (unsafe && args 2) || return 1
        split $context
        val=$(force $left)
        split $right
        prog=$(app "$left" "$val")
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
        yz=$(simplify $(app "$y" "$z"))
        prog=$(app3 "$x" "$z" "$yz")
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
        prog=$(app3 "$x" "$z" "$y")
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
        yz=$(simplify $(app "$y" "$z"))
        prog=$(app "$x" "$yz")
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
    # run reduce_ in a new scope
    echo $(reduce_ $*)
}
reduce_() {
    prog=$*
    context=end

    if [ z$TRACE = zy ]; then
        echo >&2
        echo "$INDENT   $prog" >&2
    fi
    while reduce1; do
        prog_=$(repack "$context" "$prog")
        if [ z$TRACE = zy ]; then
            echo >&2
            echo "$INDENT-> $prog_" >&2
        fi
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

#
# lambda calculus
#

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
            if [ $x = "$right" ]; then
                # eta-reduce
                echo "$left"
            else
                # c: compose
                app3 c "$left" "$(lam $x $right)"
            fi
        else
            err lam
        fi
    fi
}
lam() {
    lam_ $(echo $*)
}

# compile a normalish lambda-calculus syntax to combinatory logic.
# application is written with a space.
# \X.t is written as ^ X [ t ].
#   (use uppercase variables because if you use a variable
#    whose name is the same as a combinator things will go weird.)
# if t is atomic you can write ^ X t instead.
# atomic terms are variables, combinators and lambdas.
# square brackets [ ] are used for grouping.

compile() {
    echo $(compile_ $(echo $*))
}

compile_() {
    prog=
    stack=end
    # prog is the bit of the program so far parsed.
    # the "emit" function (below) takes a term and
    # applies prog to it, updating prog.
    # prog may be empty: emit takes care of this.
    #
    # when we encounter a variable or combinator,
    # we just emit it (apply prog to it).
    #
    # on [, we push prog on the stack, and then clear prog.
    #
    # on ], we pop a term off the stack into prog,
    # and then emit the old contents of prog.
    #
    # on ^ X, we push both prog and X, and set prog to ^.
    # thus lambda abstraction is a little bit different
    # from everything else.
    # if we emit a term while prog is ^, we must generate
    # a lambda abstraction instead of an application.
    # "emit" takes care of this too.

    while [ $# -ne 0 ]; do
        case $1 in
        "[")
            stack=$(app "$prog" "$stack")
            prog=
            shift
            ;;
        "^")
            var=$2
            stack=$(app "$prog" "$stack")
            stack=$(app "$var" "$stack")
            prog=^
            shift 2
            ;;
        "]")
            if [ "$stack" = end ]; then
                err mismatched brackets: too many "]"s
            else
                oldprog=$prog
                split $stack
                prog=$left
                stack=$right
                emit $oldprog
                shift
            fi
            ;;
        *)
            emit $1
            shift
            ;;
        esac
    done

    case $stack in
    end)
       echo $prog
       ;;
    *)
       err mismatched brackets: not enough "]"s
       ;;
    esac
}

# see comment for "compile"
emit() {
    case z$prog in
    z^)
        split $stack
        var="$left"
        split $right
        export prog="$left"
        export stack="$right"
        emit $(lam $var $*)
        ;;
    z)
        export prog="$*"
        ;;
    *)
        prog=$(simplify $(app "$prog" "$*"))
        export prog
        ;;
    esac
}

#
# an example
#

# y combinator
y_="^ X [ F [ X X ] ]"
y="^ F [ $y_ $y_ ]"

# church numerals
z="^ S ^ Z Z"
s="^ N ^ S ^ Z [ S [ N S Z ] ]"
isz="^ N ^ T ^ F [ N [ ^ _ F ] T ]"
plus="^ M ^ N [ M $s N ]"

# conversion & i/o of church numerals
fromch="^ N [ N succ 0 ]"
print="[ c echo $fromch ]"
input="^ K [ force [ toch read ] K ]"

# gödel-style lists
nil="^ N ^ C N"
cons="^ X ^ Xs ^ N ^ C [ C Xs X [ Xs N C ] ]"
null="^ Xs ^ T ^ F [ Xs T [ ^ _ ^ _ ^ _ F ] ]"

# read a list of numbers terminated by a 0
readlist="
  ^ K [
  [ $y
  ^ Loop ^ Acc [
    $input
      ^ N [
        $isz N
          [ K Acc ]
          [ Loop [ $cons N Acc ] ] ] ] ] $nil ]"

writelist="
  ^ Xs [
    force [
      Xs nil ^ _ ^ Y ^ Ys [
        force [ $fromch Y ] ^ Z [
          force Ys ^ Zs [
            Z Zs
          ]
        ]
      ]
    ] echo ]"

foldr="
  ^ Op ^ E ^ Xs
    [ Xs E [ ^ _ Op ] ]"

replicate="^ N ^ X [ N [ $cons X ] $nil ]"

drop1="^ Xs [ Xs $nil [ ^ Ys ^ _ ^ _ Ys ] ]"
drop="^ N ^ Xs [ N $drop1 Xs ]"

# example 1
# this program reads in numbers until you type in 0,
# then it prints their sum.

sum="
  [ $y
      ^ Loop ^ Acc [
        $input
          ^ N [
            $isz N
              [ $print Acc ]
              [ Loop [ $plus Acc N ] ]
          ] ] ] $z"

# try it out:
reduce $(compile $sum)

# example 2
# insertion sort!

leq="^ M ^ N [
  $null [ $drop N [ $replicate M unit ] ] ]"

insert="
  ^ X ^ Xs
    [ Xs [ $cons X $nil ]
      [ ^ Ys ^ Y ^ IYs
        [ $leq X Y
          [ $cons X [ $cons Y Ys ] ]
          [ $cons Y IYs ] ] ] ]"

sort="[ $foldr $insert $nil ]"


# try it out:
reduce $(compile "$readlist [ c $writelist $sort ]")
# type in numbers, 0 to end.
# to see the output, grep for "The answer is".
# warning: it is very very slow! :)
