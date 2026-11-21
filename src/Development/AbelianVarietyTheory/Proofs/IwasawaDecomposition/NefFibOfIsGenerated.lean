import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.TrueGeo.OfLattice

section Rect

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {B : LB X} {α β : Type} [Fintype α] [Fintype β]

def combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : Weight p σ B :=
  Weight.fs hB _ (fun _ => Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (secVal_mem _)) h

theorem combWeight_φ (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (i : B.ι) (y : CxPts p σ) :
    (combWeight hB s A h).φ i y = Real.log (∑ a, ‖∑ j, A j a * valR y.1 (B.U i) ((s j).f i)‖ ^ 2) := by
  simp only [combWeight, Weight.fs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem isCInf_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : (combWeight hB s A h).IsCInf := fun i y hy => by
  have hs : ContDiff ℝ ∞ fun v : α → ℂ => ∑ a, ‖∑ j, A j a * v j‖ ^ 2 :=
    ContDiff.sum fun a _ => (ContDiff.sum fun j _ =>
      contDiff_const.mul (contDiff_apply ℝ ℂ j)).norm_sq ℂ
  refine ⟨B.U i, α, inferInstance, fun j => (s j).f i,
    fun v => Real.log (∑ a, ‖∑ j, A j a * v j‖ ^ 2), {v | ∑ a, ‖∑ j, A j a * v j‖ ^ 2 ≠ 0}, hy,
    isOpen_ne_fun hs.continuous continuous_const, ?_, hs.contDiffOn.log fun _ h => h,
    .of_forall fun z => combWeight_φ hB s A h i z⟩
  have := (h.sum_pos hy).ne'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this

theorem semiPosReg_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (D : ℕ) :
    (combWeight hB s A h).SemiPosReg D := fun i c y hy ξ => by
  let G (a : β) (v : V D) : ℂ := ∑ j, A j a * ev p σ _ ((s j).f i) (c.e.symm v)
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hG (a) : ContDiffAt ℂ 2 (G a) (c.e y) := ContDiffAt.sum fun j _ => contDiffAt_const.mul
    (((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho (c.holo _ ((s j).f i))).contDiffAt
      (ho.mem_nhds (mem_over c.e hy.1 hy.2))).of_le (by norm_cast))
  have e (v : V D) : ∑ a, Complex.normSq (G ((Fintype.equivFin β).symm a) v) = ∑ a, ‖G a v‖ ^ 2 :=
    (Equiv.sum_comp (Fintype.equivFin β).symm fun a => Complex.normSq (G a v)).trans
      (Finset.sum_congr rfl fun a _ => Complex.normSq_eq_norm_sq _)
  have h0 := h.sum_pos hy.2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  have := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (u := fun a v => Complex.normSq (G ((Fintype.equivFin β).symm a) v))
    (fun a => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun a => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _))
    (by rw [e]; simp only [G, c.e.left_inv hy.1]; exact h0) ξ
  simp only [e] at this
  simp only [combWeight_φ]
  exact this

variable [DecidableEq β]

theorem isConj_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ σ' : k →+* ℂ} {A A' : Matrix α β ℂ}
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j))
    (h' : Weight.NoCommonZero fun a => ∑ j, A' j a • secVal p σ' (s j)) {U : Matrix β β ℂ}
    (hU : U ∈ Matrix.unitaryGroup β ℂ) (e : A' = A.map (starRingEnd ℂ) * U) :
    (combWeight hB s A h).IsConj (combWeight hB s A' h') := fun i y y' hy' hy => by
  rw [combWeight_φ, combWeight_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((s j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((s j).f i)) :=
    CxPts.ev_conj hy' hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, A j a * valR y.1 (B.U i) ((s j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2
  simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

def combHerm (hB : B.IsLB) (s : α → B.Sec) (A : (k →+* ℂ) → Matrix α β ℂ)
    (h : ∀ σ, Weight.NoCommonZero fun a => ∑ j, A σ j a • secVal p σ (s j))
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup β ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) :
    HermLB p where
  B := B
  isLB := hB
  φ σ := combWeight hB s (A σ) (h σ)
  cInf σ := isCInf_combWeight hB s _ _
  conj σ σ' i y y' e hy := by
    obtain rfl := eq_conj_of_conj e
    obtain ⟨U, hU, e'⟩ := hc σ
    exact isConj_combWeight hB s (h σ) (h _) hU e' i y y' e hy

end Rect

theorem nefFib_of_isGenerated {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (L : HermLB p) (hL : IsGenerated L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have := hX.finite
  have : IsProper p := CommonModel.isProper_of_isProjOver hX.isProjOver
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hX.isProjOver
  have hA := hH.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 ((hL.pull i).isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable {F : Type} [Field F] [NumberField F]

section Values

variable {K : Type} [Field K] {Y : Var F} (y : Sp K ⟶ Y.X) {τ : F →+* K}

omit [NumberField F] in

theorem valAt_const (hy : y ≫ Y.str = spMap τ) (a : F) : valAt y (algebraMap F Y.Fn a) = τ a := by
  refine (SmallSec.valAt_fnOf (y := y) (U := ⊤) trivial trivial (DVR.FlatBC.algX Y.str ⊤ a)).trans ?_
  refine (Points.valR_appLE y Y.str (U := ⊤) (V := ⊤) le_top (Points.le_preimage_top y) _).trans ?_
  rw [hy]
  exact Points.valR_specMap (CommRingCat.ofHom τ) a

end Values

theorem injective_emb (σ : 𝓞 F →+* ℂ) : Function.Injective σ :=
  (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _))

def extEmb (σ : 𝓞 F →+* ℂ) : F →+* ℂ := IsFractionRing.lift (injective_emb σ)

theorem extEmb_comp (σ : 𝓞 F →+* ℂ) : (extEmb σ).comp (algebraMap (𝓞 F) F) = σ :=
  RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) (injective_emb σ) a

theorem extEmb_eq {σ : 𝓞 F →+* ℂ} {τ : F →+* ℂ} (h : τ.comp (algebraMap (𝓞 F) F) = σ) : extEmb σ = τ :=
  IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun ((extEmb_comp σ).trans h.symm) a

variable [StarRing F]

end GlobalTheory.TrueGeo.OfLattice
