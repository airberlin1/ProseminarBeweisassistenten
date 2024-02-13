-- alle Beispiele, wie sie in meinem Vortrag drankamen

-- for Tactics?
theorem tacticsIntro : ∃ (p : Nat),  p = 5 := by
  exists 5

theorem tacticsMoreAdvanced (n : Nat) (h : n = 2) : n + n = 4 := by
  revert h
  intro h
  rw [h]

#print tacticsMoreAdvanced


-- for Apply

theorem applyIntro : ∀ (p q : Prop), p ∧ q → p := by
  apply And.left

theorem applyMoreAdvanced (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro
  exact hp
  exact hq


-- for Intro

theorem introIntro (α : Type) :  α → α := by
  intro (h : α)
  exact h

#print introIntro

theorem introMoreAdvanced (x y : Nat) : x = 2 → y = 2 → x + y = 4 := by
  intro (hx: x =2) hy
  rw [hx]; rw [hy]

-- more Intro examples

theorem introImplicitMatch (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  
  intro ⟨w, And.intro hpw hqw⟩
  exact ⟨w, hqw, hpw⟩

#print introImplicitMatch

theorem introForall : ∀ (α : Nat), α + 0 = α := by
  intro a
  exact Nat.add_zero a

theorem introsIntro ( a b c : Nat) : a = b → a = c → c = b := by
  intros 
  apply Eq.trans
  apply Eq.symm
  repeat assumption

-- for Cases
theorem casesIntro (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left =>
    exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

theorem casesWithDots (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

theorem casesCombined (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    . exact hq
    . exact hp
  . exact hp

-- for cases again, this time the 'real' cases
theorem casesUnstructured (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

theorem casesStructured (p q : Prop) : p ∨ q → q ∨ p := by
  intro h 
  cases h with
  | inl hp => apply Or.inr; assumption
  | inr hq => apply Or.inl; assumption

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


