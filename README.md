# A Little Scheme in Go

This is a small interpreter of a subset of Scheme.
It implements the same language as
[little-scheme-in-python](https://github.com/nukata/little-scheme-in-python).
As a Scheme implementation, 
it optimizes _tail calls_ and handles _first-class continuations_ properly.

```
$ go build
go: finding github.com/nukata/goarith v0.2.0
go: downloading github.com/nukata/goarith v0.2.0
go: extracting github.com/nukata/goarith v0.2.0
$ ./little-scheme-in-go
> (+ 5 6)
11
> 
```
