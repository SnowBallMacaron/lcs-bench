import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Completeness.Search.Variables
import Attach
import LCS.FirstOrder.Completeness.Search.RenamingApart.ProofsStamp

/-! # Free and bound variables of the input sequent (Section 5.5.1)

Using Lemma 5.3.4, the bound variables of a possibly infinite input sequent can be
renamed so that no variable free in it occurs bound in it.
Source: Logic for Computer Science, Gallier 2015
-/
