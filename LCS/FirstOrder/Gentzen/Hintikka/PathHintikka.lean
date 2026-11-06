import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.SearchTree
import LCS.FirstOrder.Gentzen.Hintikka.FreeSubstitution

/-! # The signed set of a path is a Hintikka set (proof of Theorem 5.4.1)

The claim in the proof of Theorem 5.4.1: along a path of the search tree that
does not close, the signed formulae satisfy H0-H5 with respect to the term
algebra of safe terms.
Source: Logic for Computer Science, Gallier 2015
-/
