import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.SearchTree
import LCS.FirstOrder.Gentzen.Hintikka.FreeSubstitution

/-! # Construction of the search tree for an input sequent (Section 5.4.7)

Absence of equality is preserved by every step, and the search tree data is
built for an input sequent in which no free variable occurs bound.
Source: Logic for Computer Science, Gallier 2015
-/
