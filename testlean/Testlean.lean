

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

theorem exactIntro (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro
  exact hp
  exact hq

theorem introIntro (α : Type) :  α → α := by  -- this is found exactly in the provided pdf
  intro h
  exact h

theorem rwIntro (x y : Nat) : x = y → y = x := by
  intro h
  rw [h]

theorem introMoreAdvanced (x y : Nat) : x + 0 = y → x = y := by
  intro h
  rw [add_zero] at h
  exact h

-- for Cases


-- for further Tactics

-- tasks for second half (with solutions)

