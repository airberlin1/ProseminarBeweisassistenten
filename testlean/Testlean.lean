

theorem add_zero (x : Nat) : x + 0 = x := by
  sorry

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr


theorem exampleSelfImplication (α : Type) : α → α := by
  intro a
  exact a

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

example : 2 + 3 = 5 := by
  admit

example : 2 + 3 = 5 := 
  sorry
  

#print exampleSelfImplication












-- examples for presentation

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
  apply hp
  apply hq



































-- for Intro

theorem introIntro (α : Type) :  α → α := by  -- this is found exactly in the provided pdf
  intro h
  exact h

#print introIntro

theorem introMoreAdvanced (x y : Nat) : x = 2 → y = 2 → x + y = 4 := by
  intro hx hy
  rw [hx]; rw[hy]






-- more Intro examples

theorem introImplicitMatch (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

#print introImplicitMatch

theorem introForall : ∀ (α : Nat), α + 0 = α := by
  intro a
  apply Nat.add_zero 

theorem introsIntro ( a b c : Nat) : a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

-- for Cases


-- for further Tactics

-- Admit
example (a : Nat) (ha : a * 4 = 5) : a = 2 := by
  admit

-- Assumption
example (p q : Nat) (hq : q = 2) (hp : p = 3) : p = 3 := by
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

-- Constructor?



-- tasks for second half (with solutions)

