import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlaceExtensionValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues (IsCoefExt RationalValues RationalValuesAt ValuesIn)
open GlobalTheory.Proof.PlaceExtensionValues

namespace GlobalTheory.RationalValuesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' c'' : VV K' lam →ₛₗ[σ'] W}

theorem exists_basis_val (lam : I → DomWeight n) (ι : K →+* K') (j : VVIdx lam) :
    ∃ v : VV K lam, ((bVV K' lam j : VV K' lam) : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) := by
  obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc ι lam j
  exact ⟨⟨F, hF⟩, (bVV_coe _ _ _).trans hj⟩

theorem ext_unique (h : IsCoefExt ι lam c₀ c') (h' : IsCoefExt ι lam c₀ c'') : c' = c'' := by
  refine (bVV K' lam).ext fun j => ?_
  obtain ⟨v, hv⟩ := exists_basis_val lam ι j
  rw [h v _ hv, h' v _ hv]

end Coef

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem existsUnique_c0BC (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    (hσ : σ'.comp jL = D.what₂.embLL) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃! c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' c₀ c' := by
  obtain ⟨c', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (FWT.lamV D i) c₀
  exact ⟨c', hc, fun c'' hc'' => ext_unique ((isCoefExt_iff_c0BC R i jL c₀ c'').2 hc'') ((isCoefExt_iff_c0BC R i jL c₀ c').2 hc)⟩

end Row

end GlobalTheory.RationalValuesObj

end
