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
example : ∃ (p : Nat),  p = 5 := by  -- by starts tactics block
	exists 5                         -- tactics are used to provide a proof
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

# Cases

# Weitere Tactics

# Aufgaben

