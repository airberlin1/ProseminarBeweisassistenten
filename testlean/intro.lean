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

