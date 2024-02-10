









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

theorem introIntro (α : Type) :  α → α := by
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

-- for cases again, this time the real cases
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
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp

theorem casesMore (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption --vielleicht nucht

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


-- tasks for second half (with solutions)
variable (p q r : Prop) 

example : (p → (q → r)) ↔ (p ∧ q → r) := by
  -- solution
  apply Iff.intro
  . intro hp hq
    apply hp
    exact And.left hq
    exact And.right hq
  . intro hp hq hr
    apply hp
    apply And.intro
    repeat assumption

example (p q : Prop) : p ∧ q → p ∨ q := by
  -- solution
  intro h
  cases h
  apply Or.inl
  assumption

example (α : Type) (p q : α → Prop) : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  -- solution
  intro hq hp x
  exact hq x (hp x)

theorem pImpliesP (q : Type) : p → q → p := by
  intros
  assumption

example (α : Type) : α → ((∀ x : α, r) ↔ r) := by
  -- solution
  intro ha
  apply Iff.intro
  . intro h
    exact h ha
  . exact pImpliesP r α

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  -- solution
  apply Iff.intro
  . intro h
    apply And.intro  
    . cases h
      . apply Or.inl
        assumption
      . apply Or.inr
        rename_i h
        revert h
        exact And.left
    . cases h
      . apply Or.inl
        assumption
      . apply Or.inr
        rename_i h
        revert h
        exact And.right
  . intro h
    cases h with
    | intro left right =>
      cases left
      . apply Or.inl 
        assumption
      . cases right 
        . apply Or.inl
          assumption
        . apply Or.inr
          apply And.intro
          repeat assumption

example (x : Nat) : x ≤ 0 → x = 0 := by
  -- solution
  intro hx
  cases hx with
  | refl => rfl




-- hier noch ein paar Dinge, die durch Dinge bewiesen werden, die nicht in meinem Vortrag drankommen
example (x y : Nat) (hx: x ≤ y) : ∃ (a : Nat), x + a = y := by
  -- solution
  -- this is bad because it uses rw and induction
  induction y with
  | zero =>
    rw [Nat.zero_eq] at hx
    rw [Nat.zero_eq]
    exists 0
    rw [Nat.add_zero]
    apply Nat.eq_zero_of_le_zero
    assumption  
  | succ d hd =>
    cases hx
    . exists 0
    . rename_i hb
      revert hb
      rw [Nat.le_eq]
      rw [Nat.succ_eq_add_one]
      intro hb
      apply Exists.elim (hd hb)
      intro a ha
      exists (a + 1)
      rw [← Nat.add_assoc]
      rw [ha]

example (x y : Nat) (hx : x = 3) (hy : x + y  = 6) : x = y := by
  -- solution
  -- this is bad because it uses rw
  rw [hx] at hy
  rw [hx]
  apply Eq.symm
  apply Nat.add_left_cancel
  rw [hy]

