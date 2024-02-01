# First read general
these notes are made outside of a lean environment and I am too lazy to copy unicode characters around, so here are some escape sequences that might not be accurate
## definining constants
```lean
def m : Nat := 1
def name : type := value
```

## checking types
```lean
#check m
#check expression
```

## comments
```lean
expression -- comment
/-
comment
-/
```

## evaluating an expression
```lean
#eval 5 * 4
#eval expression
```


## accessing individual components
```lean
def a : Nat \times Nat := (1, 1)
def a.1 : Nat := 1
def a.2 : Nat := 2
```

## function abstraction
```lean
#check fun (x : Nat) => x + 5
#eval (fun x : Nat => x + 5) 10   -- 15
```

there is a #print statement, not sure what it does yet

limiting scopes of variables
```lean
section useful
  variable (\a \b \g : Type)
  variable (g : \b \to \g) (f : \a \to \b) (h : \a \to \a)
  variable (x : a)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```
variables are now only defined in the section they are declared in. Note that variables are not for holding specific values but rather for having a certain type

a similar thing can be achieved with namespaces and definitions, however the scope can be reopened (or accessed by using namespacename.definition name

## useful unicode shortcuts
| Escape Sequence | Description |
| ---- | ------ |
| \to or \r | right arrow     | 
| \times | kartesian product  | 
| \a | alpha | 
| \b | beta |
| \g | gamma |
| \and | logic and |
| \or | logic or |
| \iff | equivalence |
| \l | left arrow |
|\rangle | komische Dreiecksklammer zu |
| \langle | die Klammer auf |
| \forall | forall Zeichen |
| \ex | exists Zeichen |
| \n | logic not |




# First read tactics
- alternative approach to construcitng proofs
- instructions on building a proof
- should enable more automation, but can be harder to read at times

## steps
- create a goal by starting a theorem or by introdunve a have statement
- tactics can used instead of terms with the by keyword
```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p \and q \and p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

resulting proof terms can be seen with #print
to see live goals from the line your cursor is in, press C-c TAB (emacs) or Ctrl-Shift-Enter

use tag notation to prove certain tags
```lean
case left => exact hp
case right =>
  more tactics
  more tactics
```



## Tactics
| Tactic | Description | Use |
| ------ | ------ | ----- |
| apply | applies expression as function, can have arguments | interactive function application |
| exact | apply, but goal should be filled exactly | check goal completion |
| intro | introducing a hypothesis, mainly used to show implications (turn the start into a hypthesis) | interactive funciton abstraction |
| assumption | trys to find assumption in hyptheses to complete goal | you don't want to use exact? |
| rfl | exact rfl | you have an equal sign and both sides say the same thing |
| repeat | repeat a tactic multiple times | you want to do the same thing multiple times |
| revert | opposite of intro (kind of) | gets you an implication by moving hypthesis into the goal |
| generalize | replacing an expression in the goal with a fresh variable | you know something holds for all of a type and you have a specific of that type |
| admit | same as sorry | you cannot finish a proof right now |
| intros | intro but for multiple variable without names | you don't need to name the hypotheses you are introducing |
| cases | kind of like introducing multiple cases, but they don't need a name | you don't care about naming |



you can specify names to intro to reference later. If you do not specify names, they are not accessible





# Notizen zur Präsentation


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
- mehrere Ziele nach erstem Apply, zeigen in Live-Ansicht
- nacheinander bearbeiten der Ziele
- ändere apply zu exact
  - exact nutzen, wenn ein ziel erfüllt sein soll
  - gibt fehlermeldung, wenn kein ziel erfuellt wurde


------
reden bis hier nimmt ca. 10 min in Anspruch
------

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

----
Intros reden dauert ca. 10 min
----

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
### maybe
### Constructor
- denke nicht, dass ich das mache, muss mal Zeit angucken
### contradiction
### match
----
weitere Tactics benoetigen aktuell 8-9 min
----
