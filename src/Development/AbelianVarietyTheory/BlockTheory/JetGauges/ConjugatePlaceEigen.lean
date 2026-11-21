import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.DualLattices.CotangentSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out

structure HidaSetting (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] : Prop where
  prime : p.Prime
  algClosed : IsAlgClosed C
  charZero : CharZero C
  integers : v.Integers O
  p_lt : v (p : C) < 1
  complete : IsAdicComplete (Ideal.span {(p : O)}) O

section Places

variable {E : Type} [Field E] [NumberField E]

abbrev Ow (w : HeightOneSpectrum (𝓞 E)) : Type := w.adicCompletionIntegers E

abbrev PadicOrder (p : ℕ) [Fact p.Prime] (E : Type) [Field E] : Type := ℤ_[p] ⊗[ℤ] 𝓞 E

def toPadic (p : ℕ) [Fact p.Prime] (E : Type) [Field E] : 𝓞 E →+* PadicOrder p E :=
  (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] PadicOrder p E).toRingHom

variable [IsCMField E]

def conjInt (E : Type) [Field E] [NumberField E] [IsCMField E] : 𝓞 E ≃+* 𝓞 E :=
  (IsCMField.ringOfIntegersComplexConj E).toRingEquiv

end Places

section Eigen

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
  {R : Type} [CommRing R] (α : RingAct G R)

def LieEig (τ : R →+* O) : Type :=
  {x : LieG G // ∀ a : R, x.1 ≫ α.act a = ptMap (dualScale (τ a)) ≫ x.1}

end Eigen

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
