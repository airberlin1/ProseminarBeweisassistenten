-- for further Tactics

-- Admit
example (a : Nat) (ha : a * 4 = 5) : a = 2 := by
  admit

-- Assumption
example (p q : Nat) (_ : q = 2) (_ : p = 3) : p = 3 := by
  assumption 

-- Repeat
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro
  repeat assumption

-- Revert
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  revert h
  intro h
  apply And.intro
  case left =>
    exact And.right h
  case right =>
    exact And.left h

-- Generalize
example :  true = true := by
  generalize true = x
  rfl

example (a : Nat) (ha : a = 2) : a + 2 = 4 := by
  generalize 2 = x
  admit

-- Rewrite
example (a : Nat) (ha : a = 2) : a + 2 = 4 := by
  generalize h : 2 = x
  rw [← h]
  rw [ha]

-- Exists
example : ∃ (p : Nat),  p = 5 := by
  exists 5
 

example (α : Type) (p q : α → Prop) : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hp hq y => hp y (hq y)
