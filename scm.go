// A little Scheme in Go 1.12 v0.1 H31.03.03 by SUZUKI Hisao
package main

import (
	"bufio"
	"fmt"
	"github.com/nukata/goarith"
	"io"
	"math/big"
	"os"
	"strconv"
	"strings"
	"sync"
	"text/scanner"
	"unicode"
)

type Any = interface{}

//----------------------------------------------------------------------

// Cell represents a cons-cell.
type Cell struct {
	Car Any
	Cdr Any
}

var Nil *Cell = nil

func (j *Cell) String() string {
	return Stringify(j, true)
}

// ForEach yields each element of the list of Cells.
// cf. Enumerator in https://github.com/nukata/linq-in-go
func (j *Cell) ForEach(yield func(element Any)) {
	for j != Nil {
		yield(j.Car)
		if kdr, ok := j.Cdr.(*Cell); ok {
			j = kdr
		} else {
			panic(&ImproperListError{j.Cdr})
		}
	}
}

type ImproperListError struct {
	LastElement Any
}

//----------------------------------------------------------------------

// Symbol represents Scheme's symbol.
type Symbol string

// The mappig from string to *Symbol
var Symbols sync.Map

// Intern interns a name as a symbol.
func Intern(name string) *Symbol {
	newSym := Symbol(name)
	sym, _ := Symbols.LoadOrStore(name, &newSym)
	return sym.(*Symbol)
}

var Quote = Intern("quote")
var If = Intern("if")
var Begin = Intern("begin")
var Lambda = Intern("lambda")
var Define = Intern("define")
var SetQ = Intern("set!")
var Apply = Intern("apply")
var CallCC = Intern("call/cc")

//----------------------------------------------------------------------

type Environment = *Cell

// Closure represents a lambda expression with its environment.
type Closure struct {
	Params *Cell
	Body   *Cell
	Env    Environment
}

// Cont represents Scheme's continuation.
type Cont struct {
	Op   *Symbol
	Val  Any
	Env  Environment
	Cont *Cont
}

// NoCont means there is no continuation.
var NoCont = &Cont{}

// Stringify returns the string representation of an expression.
// Strings in the expression will be quoted if quote is true.
func Stringify(exp Any, quote bool) (result string) {
	if exp == true {
		return "#t"
	} else if exp == false {
		return "#f"
	}
	switch x := exp.(type) {
	case *Cell:
		ss := make([]string, 0, 100)
		defer func() {
			if err := recover(); err != nil {
				if ile, ok := err.(*ImproperListError); ok {
					ss = append(ss, ".")
					ss = append(ss, Stringify(ile.LastElement, quote))
				} else {
					panic(err)
				}
			}
			result = "(" + strings.Join(ss, " ") + ")"
		}()
		x.ForEach(func(element Any) {
			ss = append(ss, Stringify(element, quote))
		})
		return
	case *Closure:
		p := Stringify(x.Params, true)
		b := Stringify(x.Body, true)
		e := "()"
		if x.Env != Nil {
			e = fmt.Sprintf("#%X", x.Env)
		}
		return "#<" + p + ":" + b + ":" + e + ">"
	case *Symbol:
		return string(*x)
	case string:
		if quote {
			return fmt.Sprintf("%q", exp)
		}
	}
	return fmt.Sprintf("%v", exp)
}

//----------------------------------------------------------------------

func c(car Any, cdr Any) *Cell {
	return &Cell{car, cdr}
}

var GlobalEnv Environment = c(
	c(Intern("car"), func(x *Cell) Any {
		return x.Car.(*Cell).Car
	}), c(c(Intern("cdr"), func(x *Cell) Any {
		return x.Car.(*Cell).Cdr
	}), c(c(Intern("cons"), func(x *Cell) Any {
		return c(x.Car, x.Cdr.(*Cell).Car)
	}), c(c(Intern("eq?"), func(x *Cell) Any {
		return x.Car == x.Cdr.(*Cell).Car
	}), c(c(Intern("eqv?"), func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		if a == b {
			return true
		}
		if x := goarith.AsNumber(a); x != nil {
			if y := goarith.AsNumber(b); y != nil {
				if x.Cmp(y) == 0 {
					return true
				}
			}
		}
		return false
	}), c(c(Intern("pair?"), func(x *Cell) Any {
		c, ok := x.Car.(*Cell)
		return ok && c != Nil
	}), c(c(Intern("null?"), func(x *Cell) Any {
		return x.Car == Nil
	}), c(c(Intern("not"), func(x *Cell) Any {
		return x.Car == false
	}), c(c(Intern("list"), func(x *Cell) Any {
		return x
	}), c(c(Intern("display"), func(x *Cell) Any {
		fmt.Print(Stringify(x.Car, false))
		return Void
	}), c(c(Intern("newline"), func(x *Cell) Any {
		fmt.Println()
		return Void
	}), c(c(Intern("read"), func(x *Cell) Any {
		return ReadExpression("", "")
	}), c(c(Intern("eof-object?"), func(x *Cell) Any {
		return false // XXX
	}), c(c(Intern("+"), func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Add(goarith.AsNumber(b))
	}), c(c(Intern("-"), func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Sub(goarith.AsNumber(b))
	}), c(c(Intern("*"), func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Mul(goarith.AsNumber(b))
	}), c(c(Intern("<"), func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Cmp(goarith.AsNumber(b)) < 0
	}), c(c(Intern("="), func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Cmp(goarith.AsNumber(b)) == 0
	}), c(c(CallCC, CallCC),
		c(c(Apply, Apply),
			Nil))))))))))))))))))))

//----------------------------------------------------------------------

// EvaluateGlobally evaluates an expression in the global environment.
func EvaluateGlobally(exp Any) Any {
	return Evaluate(exp, GlobalEnv, NoCont)
}

// Done means the expression has been evaluated.
var Done Environment = &Cell{Nil, Nil}

// Evaluate evaluates an expresssion with an environment and a continuation.
func Evaluate(exp Any, env Environment, k *Cont) Any {
	for {
		for env != Done {
			switch x := exp.(type) {
			case *Cell:
				kar, kdr := x.Car, x.Cdr.(*Cell)
				switch kar {
				case Quote: // (quote e)
					exp, env = kdr.Car, Done
				case If: // (if e1 e2 e3) or (if e1 e2)
					exp, k = kdr.Car, &Cont{If, kdr.Cdr, env, k}
				case Begin: // (begin e...)
					exp, k = kdr.Car, &Cont{Begin, kdr.Cdr, env, k}
				case Lambda: // (lambda (v...) e...)
					exp = &Closure{kdr.Car.(*Cell), kdr.Cdr.(*Cell), env}
					env = Done
				case Define: // (define v e)
					v := kdr.Car.(*Symbol)
					exp, k = kdr.Cdr.(*Cell).Car, &Cont{Define, v, env, k}
				case SetQ: // (set! v e)
					pair := lookForPair(kdr.Car.(*Symbol), env)
					exp, k = kdr.Cdr.(*Cell).Car, &Cont{SetQ, pair, env, k}
				default:
					exp, k = kar, &Cont{Apply, &Cell{kdr, Nil}, env, k}
				}
			case *Symbol:
				pair := lookForPair(x, env)
				exp, env = pair.Cdr, Done
			default: // as a number, #t, #f etc.
				env = Done
			}
		}
		if k == NoCont {
			return exp
		}
		exp, env, k = applyCont(k, exp)
	}
}

// Void means the expresssion has no value.
var Void = &struct{}{}

// applyCont applies a continuation to an expression.
func applyCont(cont *Cont, exp Any) (Any, Environment, *Cont) {
	op, x, env, k := cont.Op, cont.Val, cont.Env, cont.Cont
	switch op {
	case If: // x = (e2 e3)
		c := x.(*Cell)
		if exp == false {
			if c.Cdr == Nil {
				return Void, env, k
			}
			return c.Cdr.(*Cell).Car, env, k // (e3, env, k)
		}
		return c.Car, env, k // (e2, env, k)
	case Begin: //  x = (e...)
		c := x.(*Cell)
		if x == Nil {
			return exp, Done, k
		}
		return c.Car, env, &Cont{Begin, c.Cdr, env, k}
	case Define: // x = v
		env.Cdr = &Cell{env.Car, env.Cdr}
		env.Car = &Cell{x, exp}
		return Void, Done, k
	case SetQ: // x = (v . e)
		c := x.(*Cell)
		c.Cdr = exp
		return Void, Done, k
	case Apply: // x = (arguments . evaluated)
		c := x.(*Cell)
		args, evaluated := c.Car.(*Cell), &Cell{exp, c.Cdr}
		if args == Nil {
			evaluated = reverse(evaluated)
			return applyFunction(evaluated.Car, evaluated.Cdr.(*Cell), k)
		}
		return args.Car, env, &Cont{Apply, &Cell{args.Cdr, evaluated}, env, k}
	}
	panic(fmt.Sprintf("%v for %v is not a continuation ", cont, exp))
}

// applyFunction applies a function to arguments with a a continuation.
func applyFunction(fun Any, arg *Cell, k *Cont) (Any, Environment, *Cont) {
	for {
		if fun == CallCC {
			fun, arg = arg.Car, &Cell{k, Nil}
		} else if fun == Apply {
			fun, arg = arg.Car, arg.Cdr.(*Cell).Car.(*Cell)
		} else {
			break
		}
	}
	switch fn := fun.(type) {
	case func(*Cell) Any:
		return fn(arg), Done, k
	case *Closure:
		env := prependPairs(fn.Params, arg, fn.Env)
		return &Cell{Begin, fn.Body}, env, k
	case *Cont:
		return arg.Car, Done, fn
	}
	panic(fmt.Sprintf("%v for %v is not a function", fun, arg))
}

// (a b c d) => (d c b a)
func reverse(lst *Cell) *Cell {
	result := Nil
	for lst != Nil {
		lst, result = lst.Cdr.(*Cell), &Cell{lst.Car, result}
	}
	return result
}

// b, ((a . 1) (b . 2) (c . 3)) => (b . 2)
func lookForPair(key *Symbol, alist Environment) Environment {
	for j := alist; j != Nil; j = j.Cdr.(*Cell) {
		pair := j.Car.(*Cell)
		if pair.Car == key {
			return pair
		}
	}
	panic(string(*key) + " not found")
}

// (a b), (1 2), x => ((a . 1) (b . 2) . x)
func prependPairs(keys *Cell, data *Cell, alist Environment) Environment {
	if keys == Nil {
		return alist
	}
	return &Cell{&Cell{keys.Car, data.Car},
		prependPairs(keys.Cdr.(*Cell), data.Cdr.(*Cell), alist)}
}

//----------------------------------------------------------------------

func tryToReadNumber(s string) (goarith.Number, bool) {
	z := new(big.Int)
	if _, ok := z.SetString(s, 0); ok {
		return goarith.AsNumber(z), true
	}
	if f, err := strconv.ParseFloat(s, 64); err == nil {
		return goarith.AsNumber(f), true
	}
	return nil, false
}

func SplitIntoTokens(src io.Reader) []Any {
	result := make([]Any, 0, 100)
	var scn scanner.Scanner
	scn.Init(src)
	scn.Mode = scanner.ScanIdents | scanner.ScanStrings
	scn.IsIdentRune = func(ch rune, i int) bool {
		return (unicode.IsPrint(ch) && ch != ' ' && ch != ';' &&
			ch != '(' && ch != ')' && ch != '\'' && ch != '"')
	}
	scn.Error = func(s *scanner.Scanner, msg string) {
		panic(fmt.Sprintf("%s at %s", msg, s.Position))
	}
	scn.Whitespace ^= 1 << '\n' // Don't skip new lines.
	scn.Whitespace |= 1 << '\f'
LOOP:
	for tok := scn.Scan(); tok != scanner.EOF; tok = scn.Scan() {
		switch tok {
		case ';': // Skip ;-comment
			for {
				tok = scn.Scan()
				if tok == scanner.EOF || tok == '\n' {
					continue LOOP
				}
			}
		case '\n':
			continue LOOP
		case '(', ')', '\'':
			result = append(result, tok)
		case scanner.String:
			text := scn.TokenText()
			text = text[1 : len(text)-1] // Trim quotes.
			result = append(result, text)
		case scanner.Ident:
			text := scn.TokenText()
			if text == "#t" {
				result = append(result, true)
			} else if text == "#f" {
				result = append(result, false)
			} else if n, ok := tryToReadNumber(text); ok {
				result = append(result, n)
			} else {
				sym := Intern(text)
				result = append(result, sym)
			}
		default:
			panic(fmt.Sprintf("illegal char %q at %s", tok, scn.Position))
		}
	}
	return result
}

type indexError int

func peek(tokens *[]Any) Any {
	tt := *tokens
	if len(tt) == 0 {
		panic(indexError(0))
	}
	return tt[0]
}

func pop(tokens *[]Any) Any {
	result := peek(tokens)
	*tokens = (*tokens)[1:]
	return result
}

// ReadFromTokens reads a Scheme expression from [tokens].
// [tokens] will be left with the rest of tokens, if any.
func ReadFromTokens(tokens *[]Any) Any {
	token := pop(tokens)
	switch token {
	case '(':
		y := &Cell{Nil, Nil}
		z := y
		for peek(tokens) != ')' {
			if peek(tokens) == '.' {
				pop(tokens)
				y.Cdr = ReadFromTokens(tokens)
				if peek(tokens) != ')' {
					panic(") is expected")
				}
				break
			}
			e := ReadFromTokens(tokens)
			cdr := &Cell{e, Nil}
			y.Cdr = cdr
			y = cdr
		}
		pop(tokens)
		return z.Cdr
	case ')':
		panic("unexpected )")
	case '\'':
		e := ReadFromTokens(tokens)
		return &Cell{Quote, &Cell{e, Nil}} // 'e => (quote e)
	}
	return token
}

// ReadFromTokensSafely returns ReadFromTokens' result and
// whether tokens has not run out unexpectedly.
func ReadFromTokensSafely(tokens *[]Any) (result Any, ok bool) {
	defer func() {
		if err := recover(); err != nil {
			if _, succeeded := err.(indexError); succeeded {
				ok = false
			} else {
				panic(err)
			}
		}
	}()
	return ReadFromTokens(tokens), true
}

//----------------------------------------------------------------------

// Load loads a source code from a file.
func Load(fileName string) {
	file, err := os.Open(fileName)
	if err != nil {
		panic(err)
	}
	defer file.Close()
	tokens := SplitIntoTokens(file)
	for len(tokens) != 0 {
		exp := ReadFromTokens(&tokens)
		EvaluateGlobally(exp)
	}
}

var Tokens []Any
var Lines *bufio.Scanner = bufio.NewScanner(os.Stdin)

// ReadExpression reads an expression from the standard-in.
func ReadExpression(prompt1 string, prompt2 string) Any {
	for {
		old := Tokens[:]
		if exp, ok := ReadFromTokensSafely(&Tokens); ok {
			return exp
		}
		// Here peek(tokens) or pop(tokens) failed unexpectedly.
		if len(old) == 0 {
			fmt.Print(prompt1)
		} else {
			fmt.Print(prompt2)
		}
		if !Lines.Scan() {
			if err := Lines.Err(); err != nil {
				panic(err)
			}
			return scanner.EOF
		}
		line := Lines.Text()
		newTokens := SplitIntoTokens(strings.NewReader(line))
		Tokens = append(old, newTokens...)
	}
}

// ReadEvalPrintLoop repeats read-eval-print until End-Of-File.
func ReadEvalPrintLoop() {
	for {
		exp := ReadExpression("> ", "| ")
		if exp == scanner.EOF {
			fmt.Println("Goodby")
			return
		}
		result := EvaluateGlobally(exp)
		if result != Void {
			fmt.Println(Stringify(result, true))
		}
	}
}

func main() {
	if len(os.Args) >= 2 {
		Load(os.Args[1])
		if len(os.Args) < 3 || os.Args[2] != "-" {
			return
		}
	}
	ReadEvalPrintLoop()
}
