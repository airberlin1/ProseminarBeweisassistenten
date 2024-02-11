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

