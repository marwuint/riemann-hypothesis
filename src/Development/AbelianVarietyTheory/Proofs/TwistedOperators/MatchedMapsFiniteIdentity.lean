import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLineOperatorPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZeroByLocalMaps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.KerDSub

open Filter GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

theorem polMatch_mem_algD (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') {Φ Φ'}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ') : Φ' ∈ algD G.M' B.ψ B.emb := by
  obtain ⟨T, -, m, m', f, φ, f', φ', -, hf', -, rfl, -⟩ := h
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, φ' j, (hf' j).1, (hf' j).2.1, ?_, rfl⟩
  exact Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
    by_contra h'
    exact hv ((hf' j).2.2 v h'))

theorem polMatch_zero_pure (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a')
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (hf : f ∈ G.M'.Pol B.ψ B.emb)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hv : ∀ᶠ v in cofinite, φ v = G.M'.vac v) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
    (hz : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), S ⊆ T →
      R.p' f ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ v)) = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  classical
  have hfin := Filter.eventually_cofinite.mp hv
  refine ⟨X.T ∪ S ∪ hfin.toFinset, fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx), 0, 1,
    Fin.elim0, Fin.elim0, fun _ => f, fun _ => φ, fun i => i.elim0, fun _ => ⟨hf, hφ, fun v hv' => ?_⟩, ?_, ?_, ?_⟩
  · by_contra h'
    exact hv' (Finset.mem_union_right _ (hfin.mem_toFinset.mpr h'))
  · simp
  · simp
  · rw [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_one, hz _ fun x hx =>
      Finset.mem_union_left _ (Finset.mem_union_right _ hx)]

theorem polMatch_kInf (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a') (hMt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf)
    (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) (hk : k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb) (Φ Φ')
    (hPM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ') :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ') := by
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.ArchLocalAct.exists_op_of_KInf F E σ B a (a + a') G.V G.W G.M om _ _ hMt.triple.base hMt.triple.geo.hM hMt.triple.weil k hk
  obtain ⟨A', hA'⟩ := _root_.GlobalTheory.ArchLocalAct.exists_op_of_KInf F E σ B a' (a + a') G.V' G.W G.M' om' _ _ hMt.triple.base hMt.triple.geo.hM'
    hMt.triple.weil' k hk
  have hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (A f) φ := fun f φ h1 h2 =>
    hA f _ (_root_.GlobalTheory.RestPure.rest_evI_finprod F _ φ h1 ((h2.and hMt.triple.geo.hM.std).mono fun v h => h.1.trans h.2) f)
  have hpure' : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (A' f) φ := fun f φ h1 h2 =>
    hA' f _ (_root_.GlobalTheory.RestPure.rest_evI_finprod F _ φ h1 ((h2.and hMt.triple.geo.hM'.std).mono fun v h => h.1.trans h.2) f)
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', rfl, rfl, heq⟩ := hPM
  have hR := hMt.real
  set P := G.M.Pol B.ψ B.emb with hP
  let pP : P →ₗ[ℂ] R.Pi := R.p ∘ₗ P.subtype
  have hsurj : Function.Surjective pP := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    exact hR.quot.onto
  let g : P →ₗ[ℂ] R.Pi := R.p ∘ₗ A ∘ₗ P.subtype
  have hker : LinearMap.ker pP ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have := hR.cpt k hk x.1 x.2 0 (zero_mem _) (A x.1) (A' 0) (hA x.1) (hA' 0)
      (by simpa [pP] using hx)
    simpa [g] using this
  let L : R.Pi →ₗ[ℂ] R.Pi :=
    (LinearMap.ker pP).liftQ g hker ∘ₗ (pP.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hL : ∀ x ∈ P, L (R.p x) = R.p (A x) := by
    intro x hx
    have e : (pP.quotKerEquivOfSurjective hsurj).symm (R.p x) = Submodule.Quotient.mk ⟨x, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
    rfl
  have hL' : ∀ x ∈ G.M'.Pol B.ψ B.emb, L (R.p' x) = R.p' (A' x) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.eq_top_iff'.mp hR.quot.onto (R.p' x))
    rw [← hyx, hL y hy]
    exact hR.cpt k hk y hy x hx (A y) (A' x) (hA y) (hA' x) hyx
  have hcof : ∀ {κ : Type} (ψs vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ), (∀ v ∉ T, ψs v = vac v) →
      ∀ᶠ v in cofinite, ψs v = vac v := fun ψs vac h =>
    Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
      by_contra h'
      exact hv (h v h'))
  refine ⟨T, hT, m, m', fun i => A (f i), φ, fun j => A' (f' j), φ',
    fun i => ⟨_root_.GlobalTheory.KInfPol.pol_stable_kInf F E σ B a (a + a') G.V G.W G.M om _ _ hMt.triple.base hMt.triple.geo.hM hMt.triple.weil k hk
      (f i) (hf i).1 (A (f i)) (hA (f i)), (hf i).2.1, (hf i).2.2⟩,
    fun j => ⟨_root_.GlobalTheory.KInfPol.pol_stable_kInf F E σ B a' (a + a') G.V' G.W G.M' om' _ _ hMt.triple.base hMt.triple.geo.hM' hMt.triple.weil' k hk
      (f' j) (hf' j).1 (A' (f' j)) (hA' (f' j)), (hf' j).2.1, (hf' j).2.2⟩, ?_, ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure (f i) (φ i) (hf i).2.1 (hcof _ _ (hf i).2.2)
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hpure' (f' j) (φ' j) (hf' j).2.1 (hcof _ _ (hf' j).2.2)
  · have := congrArg (LinearMap.rTensor _ L) heq
    simp only [map_sum, LinearMap.rTensor_tmul] at this
    simpa only [hL _ (hf _).1, hL' _ (hf' _).1] using this

theorem pure_sub {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

end GlobalTheory.KerDSub
