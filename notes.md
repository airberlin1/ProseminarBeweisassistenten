# First read general
these notes are made outside of a lean environment and I am too lazy to copy unicode characters around, so you will instead so escape sequences
## definining constants
```lean
def m : Nat := 1
def name : type := value
```

## checking types
```lean
#check m
#check expression
```

## comments
```lean
expression -- comment
/-
comment
-/
```
\
## evaluating an expression
```lean
#eval 5 * 4
#eval expression
```


## accessing individual components
```lean
def a : Nat \times Nat := (1, 1)
def a.1 : Nat := 1
def a.2 : Nat := 2
```

## function abstraction
```lean
#check fun (x : Nat) => x + 5
#eval (fun x : Nat => x + 5) 10   -- 15
```

there is a #print statement, not sure what it does yet

limiting scopes of variables
```lean
section useful
  variable (\a \b \g : Type)
  variable (g : \b \to \g) (f : \a \to \b) (h : \a \to \a)
  variable (x : a)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```
variables are now only defined in the section they are declared in. Note that variables are not for holding specific values but rather for having a certain type

a similar thing can be achieved with namespaces and definitions, however the scope can be reopened (or accessed by using namespacename.definition name

## useful unicode shortcuts
| Escape Sequence | Description |
| ---- | ------ |
| \to or \r | right arrow     | 
| \times | kartesian product  | 
| \a | alpha | 
| \b | beta |
| \g | gamma |






# First read tactics
- alternative approach to construcitng proofs
- instructions on building a proof
- should enable more automation, but can be harder to read at times

## steps
- create a goal by starting a theorem or by introdunve a have statement
- tactics can used instead of terms with the by keyword
```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p \and q \and p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

resulting proof terms can be seen with #print
to see live goals from the line your cursor is in, press C-c TAB (emacs) or Ctrl-Shift-Enter

use tag notation to prove certain tags
```lean
case left => exact hp
case right =>
  more tactics
  more tactics
```



## Tactics
| Tactic | Description | Use |
| ------ | ------ | ----- |
| apply | applies expression as function, can have arguments | interactive function application |
| exact | apply, but goal should be filled exactly | check goal completion |
| intro | introducing a hypothesis, mainly used to show implications (turn the start into a hypthesis) | interactive funciton abstraction |
| assumption | trys to find assumption in hyptheses to complete goal | you don't want to use exact? |
| rfl | exact rfl | you have an equal sign and both sides say the same thing |
| repeat | repeat a tactic multiple times | you want to do the same thing multiple times |
| revert | opposite of intro (kind of) | gets you an implication by moving hypthesis into the goal |
| generalize | replacing an expression in the goal with a fresh variable | you know something holds for all of a type and you have a specific of that type |
| admit | same as sorry | you cannot finish a proof right now |
| intros | intro but for multiple variable without names | you don't need to name the hypotheses you are introducing |
| cases | kind of like introducing multiple cases, but they don't need a name | you don't care about naming |



you can specify names to intro to reference later. If you do not specify names, they are not accessible





# Example ideas