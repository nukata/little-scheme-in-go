# A Little Scheme in Go

This is a small interpreter of a subset of Scheme.
It implements the same language as
[little-scheme-in-python](https://github.com/nukata/little-scheme-in-python)
(and also its meta-circular interpreter, 
[little-scheme](https://github.com/nukata/little-scheme))
in circa 700 lines of Go 1.12
(and it uses an arithmetic package,
[goarith](https://github.com/nukata/goarith), which has circa 600 lines
of Go; it has _circa 1300 lines of Go in total_).


As a Scheme implementation, 
it optimizes _tail calls_ and handles _first-class continuations_ properly.


## How to run

```
$ go build
go: finding github.com/nukata/goarith v0.2.0
go: downloading github.com/nukata/goarith v0.2.0
go: extracting github.com/nukata/goarith v0.2.0
$ ./little-scheme-in-go
> (+ 5 6)
11
> (cons 'a (cons 'b 'c))
(a b . c)
> (list
| 1
| 2
| 3
| )
(1 2 3)
> 
```

Press EOF (e.g. Control-D) to exit the session.

```
> Goodbye
$ 
```

You can run it with a Scheme script.
Examples are found in 
[little-scheme](https://github.com/nukata/little-scheme).

```
$ ./little-scheme-in-go ../little-scheme/examples/yin-yang-puzzle.scm | head

*
**
***
****
*****
******
*******
********
*********
$ time ./little-scheme-in-go ../little-scheme/scm.scm \
> < ../little-scheme/examples/nqueens.scm 
((5 3 1 6 4 2) (4 1 5 2 6 3) (3 6 2 5 1 4) (2 4 6 1 3 5))

real	0m1.611s
user	0m1.705s
sys	0m0.025s
$ 
```


Put a "`-`" after the script in the command line to begin a session 
after running the script.

```
$ ./little-scheme-in-go ../little-scheme/examples/fib90.scm -
2880067194370816120
> (globals)
(apply call/cc globals = < * - + symbol? eof-object? read newline display list n
ot null? pair? eqv? eq? cons cdr car fibonacci)
> (fibonacci 1000)
43466557686937456435688527675040625802564660517371780402481729089536555417949051
89040387984007925516929592259308032263477520968962323987332247116164299644090653
3187938298969649928516003704476137795166849228875
> 
```


## The implemented language

| Scheme Expression                   | Internal Representation             |
|:------------------------------------|:------------------------------------|
| numbers `1`, `2.3`                  | `goarith.Number`                    |
| `#t`                                | `true`                              |
| `#f`                                | `false`                             |
| strings `"hello, world"`            | `string`                            |
| symbols `a`, `+`                    | `*Symbol`                           |
| `()`                                | `nil` of `*Cell`                    |
| pairs `(1 . 2)`, `(x y z)`          | `*Cell`                             |
| closures `(lambda (x) (+ x 1))`     | `*Closure`                          |
| built-in procedures `car`, `cdr`    | `*Intrinsic`                        |
| continuations                       | `type Continuation []Step`          |


`Symbol` is defined as `type Symbol string` and its values will be
interned with `sync.Map`.

For expression types and built-in procedures, see
[little-scheme-in-python](https://github.com/nukata/little-scheme-in-python).
