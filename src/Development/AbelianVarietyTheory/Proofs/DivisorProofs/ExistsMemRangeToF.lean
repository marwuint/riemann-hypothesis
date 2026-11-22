import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel

noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneFormTest

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] {F : DefFam K G Pl0 T J} (X : CxData F.amb)

structure FormsTie : Prop where

  inner_eq : ∀ t (x y : (F.R t).S.Forms),
    ⟪X.jR t x, X.jR t y⟫_ℂ = F.v0.embedding ((F.R t).S.csum (x : (F.R t).S.Cl → (F.R t).S.V) (y : (F.R t).S.Cl → (F.R t).S.V))

  inj : ∀ t, Function.Injective (X.jR t)

  span : ∀ t, Submodule.span ℂ (Set.range (X.jR t)) = ⊤

variable {X}

end Family

end GlobalTheory.OneFormTest
