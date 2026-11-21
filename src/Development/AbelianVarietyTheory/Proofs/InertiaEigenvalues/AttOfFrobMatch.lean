import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjOfFrobeniusMatch

noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleGal
open GlobalTheory.TypeLeaf (FrobDense)

theorem exists_aut {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    (φ ψ : O →+* Qbar l) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφ' : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (hψ' : ∀ z : ℤ_[l], ψ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ γ : Qbar l ≃+* Qbar l, ∀ x, γ (φ x) = ψ x := by
  have halg : Algebra.IsAlgebraic ℤ_[l] (Qbar l) :=
    haveI := IsLocalization.isAlgebraic (R := ℤ_[l]) ℚ_[l] (nonZeroDivisors ℤ_[l])
    Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (Qbar l)
  have key : ∀ (f : O →+* Qbar l) (hf : Function.Injective f),
      (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
      letI := f.toAlgebra
      haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
      IsAlgClosure O (Qbar l) := fun f hf hf' => by
    letI := f.toAlgebra
    haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
    haveI : IsScalarTower ℤ_[l] O (Qbar l) := IsScalarTower.of_algebraMap_eq fun z => (hf' z).symm
    have hi : Function.Injective (algebraMap ℤ_[l] O) := fun x y h => by
      have := (hf' x).symm.trans ((congrArg f h).trans (hf' y))
      exact Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective this)
    exact ⟨inferInstance, Algebra.IsAlgebraic.extendScalars hi⟩
  let e := @IsAlgClosure.equiv O _ _ (Qbar l) (Qbar l) _ _ ψ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ ψ.toAlgebra _ _ |>.2 hψ) (key ψ hψ hψ') φ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ φ.toAlgebra _ _ |>.2 hφ) (key φ hφ hφ')
  exact ⟨@AlgEquiv.toRingEquiv O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e,
    fun x => @AlgEquiv.commutes O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e x⟩

variable {D : D7} {T : WDTie D.nd D.naut} {i : D.ntw.Tw} {j : FractionRing (D.ntw.O0 i) →+* ℂ}
  {ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i)} {π : D.naut.CG D.R.r} {s : ℝ}

def brEmb (i : D.ntw.Tw) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : D.ntw.O0 i →+* Qbar (D.ntw.l i) :=
  (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).comp (D.ntwbr i v hv).toLL

theorem isModel_brEmb (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    IsModel (D.ntwbr i v hv) (resDec D.nd.plOm.1 (mapRep (brEmb i v hv) ρ) v) (D.ntwbr i v hv).LL
      (mapRep (D.ntwbr i v hv).toLL (ρ.comp (DecV D.nd v).subtype)) :=
  ⟨le_rfl, by ext g a b; rfl⟩

end GlobalTheory.TripleLocal

end
