import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Completeness.Search.Part1
import LCS.FirstOrder.Completeness.Search.Part2

/-! # Input terms and variable supply for the §5.5.1 search procedure

Even indices name the input variables x₀, x₁, …; odd indices name the
reserved variables y₀, y₁, …. Input formulae use only x variables, both
free and bound. The parity renaming of `InfiniteSearch` supplies such formulae.
Admissible TERMS and AVAIL enumerations determine the initial term records
and availability streams for the occurrence language of the input.
-/

namespace LCS.FirstOrder.Completeness.Search

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables


end LCS.FirstOrder.Completeness.Search

namespace LCS.FirstOrder.SyntaxN.FormulaN

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.Search


end LCS.FirstOrder.SyntaxN.FormulaN

namespace LCS.FirstOrder.Gentzen.InfSequentN

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN


end LCS.FirstOrder.Gentzen.InfSequentN

namespace LCS.FirstOrder.Completeness.Search

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae


end LCS.FirstOrder.Completeness.Search

namespace LCS.FirstOrder.Completeness.Search

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen



open LCS.FirstOrder.Gentzen.SignedFormulae


end LCS.FirstOrder.Completeness.Search

namespace LCS.FirstOrder.Completeness
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Completeness.Search


end LCS.FirstOrder.Completeness

namespace LCS.FirstOrder.Completeness
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness.Search LCS.FirstOrder.Completeness.InfiniteSearch


end LCS.FirstOrder.Completeness

namespace LCS.FirstOrder.Completeness
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness.Search LCS.FirstOrder.Completeness.InfiniteSearch


end LCS.FirstOrder.Completeness
