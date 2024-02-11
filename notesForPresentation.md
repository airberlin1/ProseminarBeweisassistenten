

# Notizen zur Präsentation
## Set up
- Mirror Screen to Beamer:
```sh
xrandr --output HDMI-A-0 --auto --same-as eDP
```
- Increase Letter Size with C-x C-+



## Tactics?
### Interaktive Beweisführung
- Zwischenstand bei der Beweisführung wird aktiv angezeigt
- Anwenden von Funktionen und Definitionen ähnlich wie mit den Terms
- Erlaubt Automatisierung
### Strukturiertes Aufteilen von Teilzielen
- Cases im Laufe der Präsentation
- mehr dazu in der späteren Präsentation
### Erstellen eines Beweisterms
- Code wie vorher
- Ausgabe durch #print
## Beispiele zu Tactics?
### tacticsIntro
- by keyword
### tacticsMoreAdvanced
- show goal in live view
  - in VSCode with ctrlshiftreturn
### print tacticsMoreAdvanced
- zeigen, dass das bereits vorher gemacht wurde



## Apply
### Interaktives Anwenden einer Funktion
- Anwenden der Funktion nach apply auf das aktuelle Ziel
- Es können Funktionsparameter übergeben werden
### Anpassen des Ziels
- Lean fasst die Schlussfolgerung aus der Anwendung der Funktion mit dem Ziel zusammen, ein neues Ziel entsteht
- siehe Änderung in Live-Ansicht
### Erstellen von Zwischenzielen
- Aufrufen von apply kann mehrere Zwischenziele zur Folge haben
- Siehe Live-Ansicht
- Diese können nacheinander gelöst werden, später siehe cases


## Beispiele zu Apply
### applyIntro
- Anwenden von And.left, sodass das linke Element als wahr gesehen wird (denn beide muessen wahr sein)
- Live-Ansicht zeigen
### applyMoreAdvanced
```lean
theorem applyMoreAdvanced (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro
  apply hp
  apply hq

```
- mehrere Ziele nach erstem Apply, zeigen in Live-Ansicht
- nacheinander bearbeiten der Ziele
- ändere apply zu exact
  - exact nutzen, wenn ein ziel erfüllt sein soll
  - gibt fehlermeldung, wenn kein ziel erfuellt wurde


## Intro Folie 1
### Einführen von Variablen
- führt variablen ein, zum Beispiel für Implikationen, Behauptungen
- wie abstrakte Funktionen, aber interaktiv


## Beispiele zu Intro
### introIntro
- Implikation wird umgewandelt in Annahme und Ziel
  - Live-Ansicht zeigen!
- wird bennant nach dem wert, den wir angeben (hier h)
- print ausgabe zeigen
  - Fukntion wird erstellt
### introMoreAdvanced
- mehrere Variablen, die eingeführt werden
- rw ist egal hier
- hinweisen auf das Semikolon und die zwei tactics in einer Zeile

## Intro Folie 2
- Einführen von Variablen für Exists, Forall
  - wie Sei bel. oder wir betrachten das x, das existiert
- automatisches Matchten (auch match kann in Tactics verwendet werden)
- intros statt intro nutzen, um so viele Variablen wie möglich ohne Namensgebung zu einzuführen
  - Namen können dann auch nicht verwendet werden 2
  - geht mit rename_i, dann werden inaccessible names neu benannt


## mehr Beispiele
### introImplicitMatch
- kann wie match genutzt werden
  - siehe match im ausgegebenen Term
- Einführen von Variablen für Exists
### introForall
- Einführen von Variablen für Forall
- kein exact, weil Type übereinstimmen müsste
  - exact ohne intro
### introsIntro
- Einführen von mehreren Variablen für die Einzelnen Annahmen
- Beweis dann über mehrere Cases
  - zeigen der Live-Ansicht!


## Cases
### verschiedene Zwischenziele
- können verschieden erzeugt werden
- case Name => lässt das Ziel lösen, welches durch Name benannt ist
- . Notation, wenn Namen nicht bekannt oder nicht wichtig sind
## Beispiele zu Cases 1
### casesIntro
- And.intro teilt hypothese und Ziel in verschiedene Cases auf
- Es können sich auch die Annahmen unterscheiden!
- mit case right bzw. case left kann ein case ausgewählt werden, der behandelt werden soll
- Es kann in der nächsten Zeile eingerückt weitergeschrieben werden oder in derselben Zeile
### casesWithDots
- es passiert das gleiche wie mit namen
- Cases werden in Reihenfolge der Aufzählung in Live-Ansicht bearbeitet
- Wenn unsicher, was aktueller case ist, Live-Ansicht nutzen
### casesCombined
- wir können die Schreibweise beliebig kombinieren

## noch eine Cases Folie
- wie können wir solche Abzweigungen selbst herbeiführen oder kontrollieren
- Strukturiert wie match aus vorherigem Vortrag
- Unstrukturiert mit Schreibweise wie oben
## mehr Beispiele
### casesUnstructured
```lean
theorem casesStructured (p q : Prop) : p ∨ q → q ∨ p := by
  intro h 
  cases h with 
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```
- Live-Ansicht!
- aufteilen des oder Ausdrucks mit cases
- beweisen der einzelnen cases

### casesStructured
- Live-Ansicht
- erlaubt unterschiedliche Reihenfolge und zugriff auf einzelne Cases mit Namen

### casesMore
- <;> wendet die Tactic auf alle cases an, die von cases erstellt wurde
- kann auch auf andere Tactics (apply) angewendet werden, die mehrere Cases erstellt

## Weitere Tactics
### Admit
- sorry für tactics
### Beispiel Admit
### Assumption
- versucht alle aktuellen Annahmen anzuwennden, um das aktuelle Ziel zu lösen
### Beispiel Assumption
- eine Annahme reicht, assumption waehlt die richtige aus
### Repeat
- mehrmaliges Ausführen einer Tactic
### Beispiel Repeat
- beide Ziele können mit assumption gelöst werden
### Revert
- Gegenteil von Intro
- kann Annahme und Ziel in eine Implikation im Ziel umwandeln
- keine Ahnung, was der Sinn sein soll
### Beispiel Revert
- zeigen, wie sich das ziel verändert
### Generalize 
- Ersetzen von Ausdruck durch eine neue Variable
- nuetzlich, wenn etwas bereits für alle Variablen eines Typs gezeigt wurde, und hier nur eine ist
- Achtung: nicht alle generalisierungen sind wahr
### Beispiel Generalize
- x = x ist wahr unabhängig von x, daher nutzen wir generalize
- rfl ist Kurzform von exact rfl
- Verfälschung des Ziels, was tun?
### Rewrite
- ersetzt Ausdruck durch einen anderen Ausdruck
- Rückgängig machen von generealize
- mehr dazu in anderem Vortrag
### Beispiel Rewrite
- Namen geben von generalization
- Nutzen von rewrite
### Exists
- angeben, welcher wert eine existenzsuche löst
### Beispiel Exists
- Beispiel vom Beginn


### Extra Time
```lean
example (α : Type) (p q : α → Prop) : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  -- solution
  intro hq hp x
  exact hq x (hp x)
```
- talk about differences, similarities
