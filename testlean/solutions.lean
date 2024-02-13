
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



































