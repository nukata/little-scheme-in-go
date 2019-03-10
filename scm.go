// A little Scheme in Go 1.12 v0.5 H31.03.03/H31.03.10 by SUZUKI Hisao
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

//----------------------------------------------------------------------

// Symbol represents Scheme's symbol.
type Symbol string

// The mapping from string to *Symbol
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

// Environment represents Scheme's environment.
type Environment struct {
	Sym  *Symbol
	Val  Any
	Next *Environment
}

// LookFor searches the environment for a symbol.
func (env *Environment) LookFor(key *Symbol) *Environment {
	for env != nil {
		if env.Sym == key {
			return env
		}
		env = env.Next
	}
	panic(string(*key) + " not found")
}

// PrependDefs builds a new environment which prepends pairs of keys and data.
func (env *Environment) PrependDefs(keys *Cell, data *Cell) *Environment {
	if keys == Nil {
		if data != Nil {
			panic("surplus arg: " + Stringify(data, true))
		}
		return env
	}
	return &Environment{keys.Car.(*Symbol), data.Car,
		env.PrependDefs(keys.Cdr.(*Cell), data.Cdr.(*Cell))}
}

//----------------------------------------------------------------------

// Step represents Scheme's step in a continuation.
type Step struct {
	Op  int
	Val Any
}

// Continuation represents Scheme's continuation as a stack.
type Continuation []Step

// Push appends a step to the tail of the continuation.
func (k *Continuation) Push(op int, value Any) {
	*k = append(*k, Step{op, value})
}

// Pop pops a step from the tail of the continuation.
func (k *Continuation) Pop() (int, Any) {
	n := len(*k) - 1
	step := (*k)[n]
	*k = (*k)[:n]
	return step.Op, step.Val
}

// Copy copies the continuation.
func (k Continuation) Copy() Continuation {
	dst := make(Continuation, len(k))
	copy(dst, k)
	return dst
}

//----------------------------------------------------------------------

// Closure represents a lambda expression with its environment.
type Closure struct {
	Params *Cell
	Body   *Cell
	Env    *Environment
}

// Void means the expresssion has no value.
var Void = &struct{}{}

// Stringify returns the string representation of an expression.
// Strings in the expression will be quoted if quote is true.
func Stringify(exp Any, quote bool) (result string) {
	switch exp {
	case true:
		return "#t"
	case false:
		return "#f"
	case scanner.EOF: // rune(-1)
		return "#<EOF>"
	case Void:
		return "#<VOID>"
	}
	switch x := exp.(type) {
	case *Cell:
		ss := make([]string, 0, 100)
		for x != Nil {
			ss = append(ss, Stringify(x.Car, quote))
			if kdr, ok := x.Cdr.(*Cell); ok {
				x = kdr
			} else {
				ss = append(ss, ".")
				ss = append(ss, Stringify(x.Cdr, quote))
				break
			}
		}
		return "(" + strings.Join(ss, " ") + ")"
	case *Environment:
		return fmt.Sprintf("#%p", x)
	case *Closure:
		p := Stringify(x.Params, true)
		b := Stringify(x.Body, true)
		e := Stringify(x.Env, true)
		return "#<" + p + ":" + b + ":" + e + ">"
	case Continuation:
		ss := make([]string, 0, 100)
		for _, step := range x {
			p := OpStr[step.Op]
			v := Stringify(step.Val, true)
			ss = append(ss, "<"+p+":"+v+">")
		}
		return "#<" + strings.Join(ss, "\n\t") + ">"
	case func(*Cell) Any:
		return fmt.Sprintf("#<%v>", x)
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

func c(name string, fun func(*Cell) Any, next *Environment) *Environment {
	return &Environment{Intern(name), fun, next}
}

var GlobalEnv *Environment = c(
	"car", func(x *Cell) Any {
		return x.Car.(*Cell).Car
	}, c("cdr", func(x *Cell) Any {
		return x.Car.(*Cell).Cdr
	}, c("cons", func(x *Cell) Any {
		return &Cell{x.Car, x.Cdr.(*Cell).Car}
	}, c("eq?", func(x *Cell) Any {
		return x.Car == x.Cdr.(*Cell).Car
	}, c("eqv?", func(x *Cell) Any {
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
	}, c("pair?", func(x *Cell) Any {
		c, ok := x.Car.(*Cell)
		return ok && c != Nil
	}, c("null?", func(x *Cell) Any {
		return x.Car == Nil
	}, c("not", func(x *Cell) Any {
		return x.Car == false
	}, c("list", func(x *Cell) Any {
		return x
	}, c("display", func(x *Cell) Any {
		fmt.Print(Stringify(x.Car, false))
		return Void
	}, c("newline", func(x *Cell) Any {
		fmt.Println()
		return Void
	}, c("read", func(x *Cell) Any {
		return ReadExpression("", "")
	}, c("eof-object?", func(x *Cell) Any {
		return x.Car == scanner.EOF
	}, c("symbol?", func(x *Cell) Any {
		_, ok := x.Car.(*Symbol)
		return ok
	}, c("+", func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Add(goarith.AsNumber(b))
	}, c("-", func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Sub(goarith.AsNumber(b))
	}, c("*", func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Mul(goarith.AsNumber(b))
	}, c("<", func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Cmp(goarith.AsNumber(b)) < 0
	}, c("=", func(x *Cell) Any {
		a, b := x.Car, x.Cdr.(*Cell).Car
		return goarith.AsNumber(a).Cmp(goarith.AsNumber(b)) == 0
	}, &Environment{CallCC, CallCC,
		&Environment{Apply, Apply,
			nil}})))))))))))))))))))

//----------------------------------------------------------------------

// Continuation operators
const (
	IfOp = iota
	BeginOp
	LambdaOp
	DefineOp
	SetQOp
	ApplyOp
	FunCallOp
	EvalArgOp
	PushArgsOp
	SetNewEnvOp
	RestoreEnvOp
)

var OpStr = [...]string{
	"If", "Begin", "Lambda", "Define", "SetQ", "Apply",
	"FunCall", "EvalArg", "PushArgs", "SetNewEnv", "RestoreEnvOp",
}

// Evaluate evaluates an expresssion in an environment.
func Evaluate(exp Any, env *Environment) Any {
	k := make(Continuation, 0, 100)
	for {
	Loop1:
		for {
			switch x := exp.(type) {
			case *Cell:
				kar, kdr := x.Car, x.Cdr.(*Cell)
				switch kar {
				case Quote: // (quote e)
					exp = kdr.Car
					break Loop1
				case If: // (if e1 e2 e3) or (if e1 e2)
					exp = kdr.Car
					k.Push(IfOp, kdr.Cdr)
				case Begin: // (begin e...)
					exp = kdr.Car
					if kdr.Cdr != Nil {
						k.Push(BeginOp, kdr.Cdr)
					}
				case Lambda: // (lambda (v...) e...)
					exp = &Closure{kdr.Car.(*Cell), kdr.Cdr.(*Cell), env}
					break Loop1
				case Define: // (define var e)
					exp = kdr.Cdr.(*Cell).Car
					k.Push(DefineOp, kdr.Car.(*Symbol))
				case SetQ: // (set! var e)
					pair := env.LookFor(kdr.Car.(*Symbol))
					exp = kdr.Cdr.(*Cell).Car
					k.Push(SetQOp, pair)
				default: // (fun arg...)
					exp = kar
					k.Push(ApplyOp, kdr)
				}
			case *Symbol:
				pair := env.LookFor(x)
				exp = pair.Val
				break Loop1
			default: // as a number, #t, #f etc.
				break Loop1
			}
		}
	Loop2:
		for {
			// fmt.Printf("_%d", len(k))
			if len(k) == 0 {
				return exp
			}
			op, x := k.Pop()
			switch op {
			case IfOp: // x = (e2 e3)
				j := x.(*Cell)
				if exp == false {
					if j.Cdr == Nil {
						exp = Void
					} else {
						exp = j.Cdr.(*Cell).Car // e3
						break Loop2
					}
				} else {
					exp = j.Car // e2
					break Loop2
				}
			case BeginOp: //  x = (e...)
				j := x.(*Cell)
				if j.Cdr != Nil { // unless tail call...
					k.Push(BeginOp, j.Cdr)
				}
				exp = j.Car
				break Loop2
			case DefineOp: // x = var
				env.Next = &Environment{env.Sym, env.Val, env.Next}
				env.Val = exp
				env.Sym = x.(*Symbol)
				exp = Void
			case SetQOp: // x = &Environment{var, e, ...}
				pair := x.(*Environment)
				pair.Val = exp
				exp = Void
			case ApplyOp: // exp = fun; x = arg...
				j := x.(*Cell)
				if j == Nil {
					exp = applyFunction(exp, Nil, &k, env)
				} else {
					k.Push(FunCallOp, exp)
					for j.Cdr != Nil {
						k.Push(EvalArgOp, j.Car)
						j = j.Cdr.(*Cell)
					}
					exp = j.Car
					k.Push(PushArgsOp, Nil)
					break Loop2
				}
			case PushArgsOp: // x = evaluated arg...
				args := &Cell{exp, x}
				op, exp = k.Pop()
				if op == EvalArgOp { // exp = next arg
					k.Push(PushArgsOp, args)
					break Loop2
				} else if op == FunCallOp { // exp = evaluated fun
					exp = applyFunction(exp, args, &k, env)
				} else {
					panic("unexpected " + OpStr[op])
				}
			case SetNewEnvOp, RestoreEnvOp: // x = &Environment{...}
				env = x.(*Environment)
			default:
				panic("Bad " + Stringify(k, true) +
					" for " + Stringify(exp, true))
			}
		} // end Loop2
	}
}

// applyFunction applies a function to arguments with a continuation.
func applyFunction(fun Any, arg *Cell, k *Continuation, env *Environment) Any {
	// fmt.Println("\t-- %s", Stringify(*k, true))
	for {
		if fun == CallCC {
			fun, arg = arg.Car, &Cell{k.Copy(), Nil}
		} else if fun == Apply {
			fun, arg = arg.Car, arg.Cdr.(*Cell).Car.(*Cell)
		} else {
			break
		}
	}
	switch fn := fun.(type) {
	case func(*Cell) Any:
		return fn(arg)
	case *Closure:
		n := len(*k) - 1
		if !(n >= 0 && (*k)[n].Op == RestoreEnvOp) { // unless tail call...
			k.Push(RestoreEnvOp, env)
		}
		k.Push(BeginOp, fn.Body)
		k.Push(SetNewEnvOp, fn.Env.PrependDefs(fn.Params, arg))
		return Void
	case Continuation:
		*k = fn.Copy()
		return arg.Car
	}
	panic(fmt.Sprintf("%v for %v is not a function", fun, arg))
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

// SplitIntoTokens splits a source text into tokens.
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

// ReadFromTokens reads a Scheme expression from tokens.
// `tokens` will be left with the rest of tokens, if any.
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
		Evaluate(exp, GlobalEnv)
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
		result := Evaluate(exp, GlobalEnv)
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
