
-- for Tactics?
theorem tacticsIntro : ∃ (p : Nat),  p = 5 := by
  exists 5

theorem tacticsMoreAdvanced (n : Nat) (h : n = 2) : n + n = 4 := by
  revert h
  intro h
  rw [h]

#print tacticsMoreAdvanced

