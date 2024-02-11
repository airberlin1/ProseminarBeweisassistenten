# Tactics in Lean

# Tactics?
- Interaktive Beweisführung
  - Tactics Abschnitt wird mit "by" gestartet
  - aktuelles Ziel kann in einem zweiten Fenster verfolgt werden
    - Ctrl+Shift+Return
  - #print, um bekanntes Format mit Terms zu erhalten
- Anwenden von Funktionen von Abstraktionen
- Automatisierungen möglich
```lean
example : ∃ (p : Nat),  p = 5 := by  -- by startet einen Tactics-Abschnitt
	exists 5-- tactics werden verwendet, um die Aussage zu beweisen
```
# Apply
- apply function [parameters]
- apply ist die Interaktive Anwendung einer Funktion
- Das aktuelle Ziel wird je nach Ergebnis der Funktion angepasst
  - Aufspaltung in mehrere Ziele ist möglich
```lean
theorem applyMoreAdvanced (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro    -- teilt das Ziel in zwei einzelne Ziele, p und q
  apply hp           -- Anwenden von hp : p auf p erreicht das erste Ziel
  apply hq           -- Erreichen des zweiten (und damit letzten) Ziels
```
- nutze exact, wenn apply ein Ziel erfüllen soll
  - Lean gibt eine Fehlermeldung, falls kein Ziel erfüllt wird
```lean
theorem applyMoreAdvanced (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro    -- teilt das Ziel in zwei einzelne Ziele, p und q
  exact hp           -- Anwenden von hp : p auf p erreicht das erste Ziel
  exact hq           -- Erreichen des zweiten (und damit letzten) Ziels
```
# Intro
- Einführen neuer Variablen
- Umwandeln von Implikationen in Annahme und Ziele
```lean
theorem introIntro (α : Type) :  α → α := by
  intro h  -- erstellt (h : α)
  exact h
```
- Einführen einer Variable für forall
```lean
theorem introForall : ∀ (α : Nat), α + 0 = α := by
  intro a  -- erstellt a : Nat
  apply Nat.add_zero
```
- Implizietes Matchen mehrere Variablen
```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩  -- erstellt w : α, hpw: p w, hqw : q w
  exact ⟨w, hqw, hpw⟩
```
			- Nutze Intros, um "alle" Variablen einzuführen, ohne diese explizit zu bennen
# Cases
- Einzelne Cases können erstellt werden, die einzeln bewiesen werden
- Nutze case CaseName => oder ., um zwischen den einzelnen Cases zu unterscheiden
```lean
theorem casesIntro (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left =>  -- Schreibweise mit explizierter Namensbenennung
    exact hp
  case right =>
    apply And.intro
    . exact hq  -- Schreibweise mit .
    . exact hp
```
- Erstellen von cases mit cases Keyword
```lean 
theorem casesStructured (p q : Prop) : p ∨ q → q ∨ p := by
  intro h 
  cases h with -- erstellt cases inr mit Annahme hq und inl mit Annahme hp
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```
# Weitere Tactics
## Admit
- sorry in einem Tactics-Abschnitt
```lean
example (a : Nat) (ha : a * 4 = 5) : a = 2 := by
  admit  -- kann gerade nicht bewiesen werden, führt zu Fehlermeldung, aber nicht zu einem Kompilierfehler
```

## Assumption
- Versucht Anwendung aller aktueller Hypothesen, um das Ziel zu lösen 
```lean
example (p q : Nat) (hq : q = 2) (hp : p = 3) : p = 3 := by
  assumption   -- wendet hp an
```

## Repeat
- wiederholt eine Tactic mehrmals
```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro 
  repeat assumption   -- wendet erst hp und dann hq an
```


## Revert
- Gegenteil zu Intro
- Annahme + Ziel wird zu Implikation
```lean
theorem introForall : ∀ (α : Nat), α + 0 = α := by
  intro a
  revert a  -- macht intro rückgängig
  exact Nat.add_zero 
```

## Generalize
- Ersetzt Ausdruck durch eine neue Variable
- kann das Ziel verfälschen, zum Beispiel ein wahres Ziel unwahr werden lassen
```lean
example :  true = true := by
  generalize true = x  -- true wird ersetzt durch x
  rfl                  -- entspricht exact rfl
```

## Exists
- Nutze Exists, um einen Wert (oder Ausdruck) anzugeben, der ein Existenzproblem löst
```lean
example : ∃ (p : Nat),  p = 5 := by
  exists 5  -- p = 5 löst die Gleichung p = 5
```

# Aufgaben
Aufgaben können auch hier gefunden werden:
https://github.com/airberlin1/ProseminarBeweisassistentenAufgaben/blob/main/TacticTasks.lean
Dort sind auch die Lösungen sowie die Präsentationsdateien verlinkt.

```lean
variable {p q r : Prop}

example : p ∧ q → p ∨ q := by
  admit

example : (p → (q → r)) ↔ (p ∧ q → r) := by
  admit

example (α : Type) (p q : α → Prop) : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  admit

theorem pImpliesP (q : Type) : p → q → p := by
  admit

example (α : Type) : α → ((∀ x : α, r) ↔ r) := by
  admit

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  admit

variable {n m : Nat}

example : n ≤ 0 → n = 0 := by
  admit
```
