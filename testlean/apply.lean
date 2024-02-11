
-- for Apply

theorem applyIntro : ∀ (p q : Prop), p ∧ q → p := by
  apply And.left

theorem applyMoreAdvanced (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro
  apply hp
  apply hq
