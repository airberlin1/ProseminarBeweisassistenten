# First read general

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
\to or \r for a right arrow
\times for kartesian product
\a alpha
\b beta
\g gamma






# First read tactics



# Example ideas