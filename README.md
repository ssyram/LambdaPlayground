# LambdaPlayground
 A simple pure lambda calculus demo with binding for encoding presentation

## Features

This tool provides simple pure lambda calculus with call-by-name and call-by-value reduction. The aim of the this tool is for introducing pure lambda calculus and some well-known encoding with it, like Church encoding of natural numbers, and of Boolean.

To gain a better view of these encodings, this tool provides the feature of binding that one is able to give an English identifier name to lambda terms, then, afte rcomputation, one is able to see the result back in these names.

For example, we have Church encoding for numbers:

```
let 0 = \f x.x
let 1 = \f x.f x
let mid + = \n m f x.n f (m f x)  // "mid" is for infix operator definition
```

So we gain a computation process like:
```
0 + 1
1 : -> (\m.\f.\x.0 f (m f x)) 1
2 : -> \f.\x.0 f (1 f x)
3 : -> \f.\x.0 f ((\x.f x) x)
4 : -> \f.\x.0 f (f x)
5 : -> \f.\x.(\x.x) (f x)
6 : -> 1
-/->
= 1
```

This is, however, not a normal reduction for both call-by-value and call-by-name reduction strategy, both of which are supposed to terminate when reaching single lambda abstraction. This is why the tool introduces "recursive value mode" here, that the reduction terminates when no redex exists.

Note that the user-defined names are fundamentally and purly syntactic suger that the internal presentation is just a pure lambda term. Hence, recursive definition is not allowed.

On the other hand, as this is just a simple demo, it is an undefined behavior if one tries to make use of the loop hole that free variables are allowed in RHS of definition to try recursive definitions.
In fact, it is not at all recommended to do that, as techniques like Y-combinator are definitely better choices.

## Deployment

As this is a pure F# project (although most of them are written in ML), just run F# is OK.

## Usage

There are three ways to use these tools: instant formula as argument of the program, read and run a file, and enter the interactive mode (which is recommended, and just run the program will lead to this mode).

Commands as argument should begin with "-" and in interactive mode should begin with "%". Nevertheless, the other forms are all the same.

Commands include:

```
help: printing out help strings
quit/exit: exit the interactive mode
rv: recursive value mode
cbn: adopt call-by-name reduction strategy
cnv: adopt call-by-value reduction strategy
clear: clear all bindings
to_value: reduction all the way to value, may lead to infinite evaluation and thus printing
max_steps <num>: in contrast to to_value, this command specify a maximum reduction number
expand: while reduction, expand all elements
sim_step: in contrast to expand, try printing out the term in user-defined strings
silent: silent mode, not printing out all strings
file/f <file path>: load a file (in interactive mode) or execute a file (in argument)
run <formula>: run a formula as command line and not triggering interactive mode
result_only: display only the result, ignoring the process of computation
red_cmp: perform reduction before comparison
```

Also, some commands (those open or close modes) can have a prefix `not` to take their opposite meaning, like `%not rv`.
