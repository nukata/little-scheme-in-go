// A little Scheme in Go 1.12 v1.0 H31.03.03/H31.03.30 by SUZUKI Hisao
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

// Length returns the length of the list.
func (j *Cell) Length() int {
	n := 0
	for j != Nil {
		n, j = n+1, j.Cdr.(*Cell)
	}
	return n
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
// (env.Sym == nil) means the env is the frame top.
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
	panic(fmt.Errorf("%s not found", *key))
}

// PrependDefs builds a new environment which prepends pairs of keys and data.
func (env *Environment) PrependDefs(keys *Cell, data *Cell) *Environment {
	if keys == Nil {
		if data != Nil {
			panic(fmt.Errorf("surplus arg: %s", Stringify(data, true)))
		}
		return env
	}
	if data == Nil {
		panic(fmt.Errorf("surplus param: %s", Stringify(keys, true)))
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
func (k *Continuation) Pop() (op int, value Any) {
	n := len(*k) - 1
	step := &(*k)[n]
	op, value = step.Op, step.Val
	step.Val = nil // for garbage collection
	*k = (*k)[:n]
	return
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

// Intrinsic represents an intrinsic function.
type Intrinsic struct {
	Name     string
	Arity    int
	Function func(*Cell) Any
}

func (f *Intrinsic) String() string {
	return fmt.Sprintf("#<%s:%d>", f.Name, f.Arity)
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
		ss := make([]string, 0, 100)
		for x != nil {
			if x == GlobalEnv {
				ss = append(ss, "GlobalEnv")
				break
			}
			if x.Sym == nil { // frame top
				ss = append(ss, "|")
			} else {
				ss = append(ss, string(*x.Sym))
			}
			x = x.Next
		}
		return "#<" + strings.Join(ss, " ") + ">"
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
			ss = append(ss, p+" "+v)
		}
		return "\n\t#<" + strings.Join(ss, "\n\t  ") + ">"
	case *Symbol:
		return string(*x)
	case string:
		if quote {
			return fmt.Sprintf("%q", exp)
		}
	case rune:
		return fmt.Sprintf("#\\%c", x)
	case []Any:
		ss := make([]string, 0, 100)
		for _, e := range x {
			ss = append(ss, Stringify(e, true))
		}
		return "#(" + strings.Join(ss, " ") + ")"
	}
	return fmt.Sprintf("%v", exp)
}

// GlobalEnv is the global environment.
var GlobalEnv *Environment

//----------------------------------------------------------------------

func c(name string, arity int, fun func(*Cell) Any,
	next *Environment) *Environment {
	return &Environment{Intern(name), &Intrinsic{name, arity, fun}, next}
}

func init() {
	GlobalEnv = &Environment{nil, nil, // frame top
		c("car", 1, func(x *Cell) Any {
			return x.Car.(*Cell).Car
		}, c("cdr", 1, func(x *Cell) Any {
			return x.Car.(*Cell).Cdr
		}, c("cons", 2, func(x *Cell) Any {
			return &Cell{x.Car, x.Cdr.(*Cell).Car}
		}, c("eq?", 2, func(x *Cell) Any {
			return x.Car == x.Cdr.(*Cell).Car
		}, c("eqv?", 2, func(x *Cell) Any {
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
		}, c("pair?", 1, func(x *Cell) Any {
			c, ok := x.Car.(*Cell)
			return ok && c != Nil
		}, c("null?", 1, func(x *Cell) Any {
			return x.Car == Nil
		}, c("not", 1, func(x *Cell) Any {
			return x.Car == false
		}, c("list", -1, func(x *Cell) Any {
			return x
		}, c("display", 1, func(x *Cell) Any {
			fmt.Print(Stringify(x.Car, false))
			return Void
		}, c("newline", 0, func(x *Cell) Any {
			fmt.Println()
			return Void
		}, c("read", 0, func(x *Cell) Any {
			return ReadExpression("", "")
		}, c("eof-object?", 1, func(x *Cell) Any {
			return x.Car == scanner.EOF
		}, c("symbol?", 1, func(x *Cell) Any {
			_, ok := x.Car.(*Symbol)
			return ok
		}, c("+", 2, func(x *Cell) Any {
			a, b := x.Car, x.Cdr.(*Cell).Car
			return goarith.AsNumber(a).Add(goarith.AsNumber(b))
		}, c("-", 2, func(x *Cell) Any {
			a, b := x.Car, x.Cdr.(*Cell).Car
			return goarith.AsNumber(a).Sub(goarith.AsNumber(b))
		}, c("*", 2, func(x *Cell) Any {
			a, b := x.Car, x.Cdr.(*Cell).Car
			return goarith.AsNumber(a).Mul(goarith.AsNumber(b))
		}, c("<", 2, func(x *Cell) Any {
			a, b := x.Car, x.Cdr.(*Cell).Car
			return goarith.AsNumber(a).Cmp(goarith.AsNumber(b)) < 0
		}, c("=", 2, func(x *Cell) Any {
			a, b := x.Car, x.Cdr.(*Cell).Car
			return goarith.AsNumber(a).Cmp(goarith.AsNumber(b)) == 0
		}, c("globals", 0, func(x *Cell) Any {
			j := Nil // Take Next initially to skip the frame top.
			for e := GlobalEnv.Next; e != nil; e = e.Next {
				j = &Cell{e.Sym, j}
			}
			return j
		}, &Environment{CallCC, CallCC,
			&Environment{Apply, Apply,
				nil}}))))))))))))))))))))}
}

//----------------------------------------------------------------------

// Continuation operators
const (
	ThenOp = iota
	BeginOp
	DefineOp
	SetQOp
	ApplyOp
	ApplyFunOp
	EvalArgOp
	PushArgsOp
	RestoreEnvOp
)

// Names of continuation operators
var OpStr = [...]string{
	"Then", "Begin", "Define", "SetQ", "Apply",
	"ApplyFun", "EvalArg", "PushArgs", "RestoreEnv",
}

// Evaluate evaluates an expresssion in an environment.
func Evaluate(exp Any, env *Environment) (result Any, err error) {
	k := make(Continuation, 0, 100)
	defer func() {
		if ex := recover(); ex != nil {
			if er, isError := ex.(error); isError {
				if len(k) == 0 {
					err = er
				} else {
					err = fmt.Errorf("%s: %s\n\t%s, %s",
						er, Stringify(k, true),
						Stringify(exp, true), Stringify(env, true))
				}
			} else {
				panic(ex)
			}
		}
	}()
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
					k.Push(ThenOp, kdr.Cdr)
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
		} // end Loop1
	Loop2:
		for {
			//fmt.Printf("_%d", len(k))
			if len(k) == 0 {
				return exp, nil
			}
			op, x := k.Pop()
			switch op {
			case ThenOp: // x = (e2 e3)
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
				if env.Sym != nil { // Check env for the frame top.
					panic(fmt.Errorf("invalid env: %s", Stringify(env, true)))
				}
				env.Next = &Environment{x.(*Symbol), exp, env.Next}
				exp = Void
			case SetQOp: // x = &Environment{var, e, ...}
				pair := x.(*Environment)
				pair.Val = exp
				exp = Void
			case ApplyOp: // exp = fun; x = arg...
				j := x.(*Cell)
				if j == Nil {
					exp, env = applyFunction(exp, Nil, &k, env)
				} else {
					k.Push(ApplyFunOp, exp)
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
				} else if op == ApplyFunOp { // exp = evaluated fun
					exp, env = applyFunction(exp, args, &k, env)
				} else {
					panic(fmt.Errorf("unexpected op %d", op))
				}
			case RestoreEnvOp: // x = &Environment{...}
				env = x.(*Environment)
			default:
				panic(fmt.Errorf("bad op %d and value %s",
					op, Stringify(x, true)))
			}
		} // end Loop2
	}
}

// applyFunction applies a function to arguments with a continuation.
func applyFunction(fun Any, arg *Cell, k *Continuation, env *Environment) (
	Any, *Environment) {
	for {
		if fun == CallCC {
			pushRestoreEnv(k, env)
			fun, arg = arg.Car, &Cell{k.Copy(), Nil}
		} else if fun == Apply {
			fun, arg = arg.Car, arg.Cdr.(*Cell).Car.(*Cell)
		} else {
			break
		}
	}
	switch fn := fun.(type) {
	case *Intrinsic:
		if fn.Arity >= 0 {
			if arg.Length() != fn.Arity {
				panic(fmt.Errorf("%s (arity %d) applied to %s",
					fn.Name, fn.Arity, Stringify(arg, true)))
			}
		}
		return fn.Function(arg), env
	case *Closure:
		pushRestoreEnv(k, env)
		k.Push(BeginOp, fn.Body)
		return Void, &Environment{nil, nil, // frame top
			fn.Env.PrependDefs(fn.Params, arg)}
	case Continuation:
		*k = fn.Copy()
		return arg.Car, env
	}
	panic(fmt.Errorf("%s applied to %s is not a function",
		Stringify(fun, true), Stringify(arg, true)))
}

func pushRestoreEnv(k *Continuation, env *Environment) {
	n := len(*k) - 1
	if !(n >= 0 && (*k)[n].Op == RestoreEnvOp) { // unless tail call...
		k.Push(RestoreEnvOp, env)
	}
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
		panic(fmt.Errorf("%s at %s", msg, s.Position))
	}
	scn.Whitespace ^= 1 << '\n' // Don't skip new lines.
	scn.Whitespace |= 1 << '\f'
Loop:
	for tok := scn.Scan(); tok != scanner.EOF; tok = scn.Scan() {
		switch tok {
		case ';': // Skip ;-comment
			for {
				tok = scn.Scan()
				if tok == scanner.EOF || tok == '\n' {
					continue Loop
				}
			}
		case '\n':
			continue Loop
		case '(', ')', '\'':
			result = append(result, tok)
		case scanner.String:
			text := scn.TokenText()
			text = text[1 : len(text)-1] // Trim quotes.
			result = append(result, text)
		case scanner.Ident:
			text := scn.TokenText()
			if text == "." {
				result = append(result, '.')
			} else if text == "#t" {
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
			panic(fmt.Errorf("illegal char %q at %s", tok, scn.Position))
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
					panic(fmt.Errorf(") is expected: %s",
						Stringify(*tokens, true)))
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
		panic(fmt.Errorf("unexpected ) before %s", Stringify(*tokens, true)))
	case '\'':
		e := ReadFromTokens(tokens)
		return &Cell{Quote, &Cell{e, Nil}} // 'e => (quote e)
	}
	return token
}

//----------------------------------------------------------------------

// Load loads a source code from a file.
func Load(fileName string) (ok bool) {
	defer func() {
		if ex := recover(); ex != nil {
			if _, isIndexError := ex.(indexError); isIndexError {
				fmt.Fprintf(os.Stderr, "error: unexpected EOF: %s\n", fileName)
			} else {
				fmt.Fprintf(os.Stderr, "error: %s\n", ex)
			}
			ok = false
		}
	}()
	file, err := os.Open(fileName)
	if err != nil {
		panic(err)
	}
	defer file.Close()
	tokens := SplitIntoTokens(file)
	for len(tokens) != 0 {
		exp := ReadFromTokens(&tokens)
		_, err = Evaluate(exp, GlobalEnv)
		if err != nil {
			panic(err)
		}
	}
	return true
}

var Tokens []Any
var Lines *bufio.Scanner = bufio.NewScanner(os.Stdin)

func splitIntoTokensSafely(src io.Reader) (result []Any, err Any) {
	defer func() {
		err = recover()
	}()
	result = SplitIntoTokens(src)
	return
}

func readFromTokensSafely(tokens *[]Any) (result Any, err Any) {
	defer func() {
		err = recover()
	}()
	result = ReadFromTokens(tokens)
	return
}

// ReadExpression reads an expression from the standard-in.
func ReadExpression(prompt1 string, prompt2 string) Any {
	var errorResult Any
	for {
		old := Tokens[:]
		if exp, err := readFromTokensSafely(&Tokens); err == nil {
			return exp
		} else if _, isIndexError := err.(indexError); !isIndexError {
			errorResult = err
			break
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
		newTokens, err := splitIntoTokensSafely(strings.NewReader(line))
		if err != nil {
			errorResult = err
			break
		}
		Tokens = append(old, newTokens...)
	}
	Tokens = make([]Any, 0) // Discard the erroneous tokens.
	return fmt.Errorf("syntax error: %v", errorResult)
}

// ReadEvalPrintLoop repeats read-eval-print until End-Of-File.
func ReadEvalPrintLoop() {
	for {
		exp := ReadExpression("> ", "| ")
		if exp == scanner.EOF {
			fmt.Println("Goodby")
			return
		} else if err, isError := exp.(error); isError {
			fmt.Println(err)
			continue
		}
		result, err := Evaluate(exp, GlobalEnv)
		if err != nil {
			fmt.Println(err)
		} else if result != Void {
			fmt.Println(Stringify(result, true))
		}
	}
}

func main() {
	if len(os.Args) >= 2 {
		if !Load(os.Args[1]) {
			os.Exit(1)
		}
		if len(os.Args) < 3 || os.Args[2] != "-" {
			return
		}
	}
	ReadEvalPrintLoop()
}
