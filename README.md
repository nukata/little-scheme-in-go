# A Little Scheme in Go

This is a small interpreter of a subset of Scheme.
It implements the same language as

- [little-scheme-in-python](https://github.com/nukata/little-scheme-in-python)
- [little-scheme-in-java](https://github.com/nukata/little-scheme-in-java)
- [little-scheme-in-cs](https://github.com/nukata/little-scheme-in-cs)

and also their meta-circular interpreter, 
[little-scheme](https://github.com/nukata/little-scheme)
in circa 750 lines of Go 1.12
(and it uses an arithmetic package,
[goarith](https://github.com/nukata/goarith), which has circa 600 lines
of Go; it has _circa 1350 lines of Go in total_).


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
[little-scheme](https://github.com/nukata/little-scheme);
download it at `..` and you can try the following:

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
$ ./little-scheme-in-go ../little-scheme/scm.scm < ../little-scheme/examples/nqu
eens.scm 
((5 3 1 6 4 2) (4 1 5 2 6 3) (3 6 2 5 1 4) (2 4 6 1 3 5))
$ 
```


Put a "`-`" after the script in the command line to begin a session 
after running the script.

```
$ ./little-scheme-in-go ../little-scheme/examples/fib90.scm -
2880067194370816120
> (globals)
(apply call/cc globals error = < * - + symbol? eof-object? read newline display 
list not null? pair? eqv? eq? cons cdr car fibonacci)
> (fibonacci 16)
987
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


- `Symbol` is defined as `type Symbol string` and its values will be
  interned with `sync.Map`.


### Expression types

- _v_  [variable reference]

- (_e0_ _e1_...)  [procedure call]

- (`quote` _e_)  
  `'`_e_ [transformed into (`quote` _e_) when read]

- (`if` _e1_ _e2_ _e3_)  
  (`if` _e1_ _e2_)

- (`begin` _e_...)

- (`lambda` (_v_...) _e_...)

- (`set!` _v_ _e_)

- (`define` _v_ _e_)

For simplicity, this Scheme treats (`define` _v_ _e_) as an expression type.


### Built-in procedures

|                      |                          |                     |
|:---------------------|:-------------------------|:--------------------|
| (`car` _lst_)        | (`not` _x_)              | (`eof-object?` _x_) |
| (`cdr` _lst_)        | (`list` _x_ ...)         | (`symbol?` _x_)     |
| (`cons` _x_ _y_)     | (`call/cc` _fun_)        | (`+` _x_ _y_)       |
| (`eq?` _x_ _y_)      | (`apply` _fun_ _arg_)    | (`-` _x_ _y_)       |
| (`eqv?` _x_ _y_)     | (`display` _x_)          | (`*` _x_ _y_)       |
| (`pair?` _x_)        | (`newline`)              | (`<` _x_ _y_)       |
| (`null?` _x_)        | (`read`)                 | (`=` _x_ _y_)       |
|                      | (`error` _reason_ _arg_) | (`globals`)         |

- `(error` _reason_ _arg_`)` panics with an `ErrorString`
  "`Error:` _reason_`:` _arg_".
  The type `ErrorString` is defined as `type ErrorString string`.
  The procedure `error`
  is based on [SRFI-23](https://srfi.schemers.org/srfi-23/srfi-23.html).

- `(globals)` returns a list of keys of the global environment.
  It is not in the standard.

See [`GlobalEnv`](scm.go#L249-L321)
in `scm.go` for the implementation of the procedures
except `call/cc` and `apply`.  
`call/cc` and `apply` are implemented particularly at 
[`applyFunction`](scm.go#L485-L518) in `scm.go`.


I hope this serves as a model of how to write a Scheme interpreter in Go.
