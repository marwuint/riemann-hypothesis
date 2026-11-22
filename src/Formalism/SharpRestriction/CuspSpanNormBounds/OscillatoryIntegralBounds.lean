import Formalism.SharpRestriction.CuspSpanNormBounds.RadialChainStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
import Formalism.SharpRestriction.CuspSpanNormBounds.HereditaryPositivity
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialLemmaE
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.YangianSpanCharacter.YangianRelationFirst
import Formalism.FormalDegreeBessel.FinalWR
import Formalism.HermitianCurvature.Statement
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Herglotz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov
import Formalism.HermitianCurvature.StatementTA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AntidiagMulDiagonal
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearCoefficients
import Formalism.NormUnitaryBounds.DetPolynomialWeights.LtSuccOfMemWeightCompositions
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeRigidity.StatementA
import Formalism.LatticeRigidity.StatementC
import Formalism.LatticeRigidity.StatementD

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

section PartA14

open Polynomial Finset

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA14

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

section PartA15

open MeasureTheory Filter Topology
open scoped ComplexConjugate BoundedContinuousFunction NNReal ENNReal

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

namespace Hz

abbrev Tor (d : ℕ) := Fin d → UnitAddCircle

def ch {d : ℕ} (n : Fin d → ℤ) (x : Tor d) : ℂ := ∏ j, fourier (n j) (x j)

theorem ch_cont {d : ℕ} (n : Fin d → ℤ) : Continuous (ch n) := by
  unfold ch
  exact continuous_finset_prod _ fun j _ => (fourier (n j)).continuous.comp (continuous_apply j)

def box (d N : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)

def fw {d : ℕ} (N : ℕ) (σ : Fin d → ℤ) : ℝ := ∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))

def fej {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) (x : Tor d) : ℂ :=
  ∑ σ ∈ box d N, ((fw N σ : ℝ) : ℂ) * φ (-σ) * ch σ x

theorem fej_cont {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) : Continuous (fej φ N) := by
  unfold fej
  exact continuous_finset_sum _ fun σ _ => continuous_const.mul (ch_cont σ)

def fmu {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) : Measure (Tor d) :=
  volume.withDensity (fun x => ((Real.toNNReal (fej φ N x).re : ℝ≥0) : ℝ≥0∞))

theorem fre_cont {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) : Continuous (fun x => (fej φ N x).re) := by
  exact Complex.continuous_re.comp (fej_cont φ N)

instance {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) : IsFiniteMeasure (fmu φ N) := by
  apply isFiniteMeasure_withDensity
  have hi : Integrable (fun x : Tor d => (fej φ N x).re) volume :=
    (fre_cont φ N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.lintegral_lt_top.ne

end Hz

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA15

section PartA16

open Complex Real MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

section Std

variable (d : ℕ)

abbrev stB : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

abbrev stL : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℤ (Set.range (stB d))

variable {d}

def zp (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 _).symm (fun j => (n j : ℝ))

lemma zp_apply (n : Fin d → ℤ) (j : Fin d) : (zp n).ofLp j = (n j : ℝ) := rfl

lemma stB_eq (i : Fin d) : stB d i = EuclideanSpace.single i (1 : ℝ) := by
  simp [stB]

lemma stB_apply (i j : Fin d) : (stB d i).ofLp j = if j = i then (1 : ℝ) else 0 := by
  rw [stB_eq]; simp [PiLp.single_apply]

lemma stB_sum (m : Fin d → ℤ) : ∑ i, m i • stB d i = zp m := by
  ext j
  simp only [WithLp.ofLp_sum, zp_apply]
  rw [Finset.sum_apply]
  simp only [PiLp.smul_apply, stB_apply, smul_ite, smul_zero]
  simp [zsmul_eq_mul]

lemma zp_injective : Function.Injective (zp (d := d)) := by
  intro x y h
  funext i
  have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v.ofLp i) h
  simp only [zp_apply] at this
  exact_mod_cast this

variable (d) in

def latE : (Fin d → ℤ) ≃ stL d :=
  Equiv.ofBijective (fun m => ⟨zp m, by
      rw [← stB_sum]
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨m, rfl⟩⟩)
    ⟨fun m m' h => zp_injective (congrArg Subtype.val h),
     fun v => by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 v.2
      exact ⟨c, Subtype.ext (by simp only; rw [← stB_sum, hc])⟩⟩

end Std

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA16

namespace Formalism.MainNotions.InterlacingSignCuts.SP

end Formalism.MainNotions.InterlacingSignCuts.SP

namespace Formalism.MainNotions.InterlacingSignCuts.SP

end Formalism.MainNotions.InterlacingSignCuts.SP

namespace Formalism.MainNotions.InterlacingSignCuts.SP

end Formalism.MainNotions.InterlacingSignCuts.SP

namespace Formalism.MainNotions.InterlacingSignCuts.SP

end Formalism.MainNotions.InterlacingSignCuts.SP

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

section PartAOm

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LevR

namespace Formalism.MainNotions.InterlacingSignCuts

theorem herm_Hb (k : ℕ) (x y : Fin (k + 1) → ℂ) :
    herm (Hb k) x y = ∑ j, star (y j) * ((if j = Fin.last k then (-1 : ℂ) else 1) * x j) := by
  unfold herm Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]

theorem wI_inj (k r : ℕ) : Function.Injective (wI k r) := by
  intro a b h
  unfold wI at h
  rw [Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem not_range_wI (k r : ℕ) (i : Fin (2 * r + k + 1)) (hi : i ∉ Set.range (wI k r)) :
    i.val < r ∨ r + k < i.val := by
  by_contra hc
  push_neg at hc
  apply hi
  refine ⟨⟨i.val - r, by omega⟩, ?_⟩
  unfold wI
  ext
  show r + (i.val - r) = i.val
  omega

theorem Hpk_wI (k r : ℕ) (j : Fin (k + 1)) (q : Fin (2 * r + k + 1)) :
    Hpk k r (wI k r j) q = if q = wI k r j then (if j = Fin.last k then (-1 : ℂ) else 1) else 0 := by
  have hj := j.isLt
  have hv : (wI k r j).val = r + j.val := rfl
  unfold Hpk
  rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega)]
  by_cases hq : q = wI k r j
  · rw [if_pos hq, if_pos ⟨by rw [hv]; omega, by rw [hv]; omega, hq.symm⟩]
    by_cases hl : j = Fin.last k
    · rw [if_pos hl, if_pos (by rw [hv, hl]; rfl)]
    · rw [if_neg hl, if_neg (by
        rw [hv]
        intro h
        exact hl (Fin.ext (by rw [Fin.val_last]; omega)))]
  · rw [if_neg hq, if_neg (by rintro ⟨_, _, h⟩; exact hq h.symm)]

theorem herm_Hpk_wb (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) (hw : inWb k r w) :
    herm (Hpk k r) v w = herm (Hb k) (wbPart k r v) (wbPart k r w) := by
  rw [herm_Hb]
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  symm
  apply Fintype.sum_of_injective (wI k r) (wI_inj k r)
  · intro i hi
    rw [hw i (not_range_wI k r i hi)]
    simp
  · intro j
    have : (Hpk k r *ᵥ v) (wI k r j) = (if j = Fin.last k then (-1 : ℂ) else 1) * v (wI k r j) := by
      simp only [Matrix.mulVec, dotProduct, Hpk_wI]
      simp
    rw [this]
    rfl

theorem wbPart_bigCell (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') :
    wbPart k r (bigCell k r c μ *ᵥ z') = μ *ᵥ wbPart k r z' := by
  funext j
  simp only [wbPart, Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective (wI k r) (wI_inj k r)
  · intro q hq
    rw [hz' q (not_range_wI k r q hq)]
    simp
  · intro j'
    have hj := j.isLt
    have hj' := j'.isLt
    have h1 : ¬ (wI k r j').val < r := by show ¬ (r + j'.val < r); omega
    have h2 : (wI k r j').val ≤ r + k := by show r + j'.val ≤ r + k; omega
    have h3 : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k := by
      constructor
      · show r ≤ r + j.val; omega
      · show r + j.val ≤ r + k; omega
    have : bigCell k r c μ (wI k r j) (wI k r j') = μ j j' := by
      unfold bigCell
      rw [dif_neg h1, dif_pos h2, dif_pos h3]
      congr 1 <;> exact Fin.ext (by show r + _ - r = _; omega)
    rw [this]

theorem bigCell_D (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ ≠ 0 ∧
    Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1)) =
      Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ * herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  obtain ⟨m1, -, m3⟩ := Formalism.QuantumDeterminants.bigCellMinors k r z z' c μ hz hz'
  have hDr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ ≠ 0 := by
    have h := m1 (Fin.last r)
    simp only [Fin.val_last] at h
    rw [h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  refine ⟨hDr, ?_⟩
  have h := m3 hc
  unfold zeta at h
  rw [herm_Hpk_wb k r _ z hz, wbPart_bigCell k r c μ z' hz', div_eq_iff hDr] at h
  rw [h, mul_comm]

end Formalism.MainNotions.InterlacingSignCuts

end PartAOm

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

section PartAGw

open MeasureTheory

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

section Abstract

variable {X Y K Q : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace K] [MeasurableSpace Q]

structure WeilData (M ν : Measure X) (Sm : Measure Y) (act : X → Y → X) (LUs : Set X)
    (μK : Measure K) (μQ : Measure Q) (κ : K → Y) (Ψ : K × Q → X) (kc : X → K) (γ : K → ℝ) : Prop where
  weil : ∀ F : X → ℂ, Integrable F M → ∫ p, F p ∂M = ∫ p, (∫ u', F (act p u') ∂Sm) ∂ν
  conc : ν LUsᶜ = 0
  emb : MeasurableEmbedding κ
  stab : Sm = Measure.map κ μK
  mp : MeasurePreserving Ψ (μK.prod μQ) M
  kc_meas : Measurable kc
  kc_Ψ : ∀ k q, kc (Ψ (k, q)) = k
  trans : ∀ p ∈ LUs, MeasurePreserving (fun k => kc (act p (κ k))) μK μK
  γ_meas : Measurable γ
  γ_int : Integrable γ μK
  γ_one : ∫ k, γ k ∂μK = 1

variable {M ν : Measure X} {Sm : Measure Y} {act : X → Y → X} {LUs : Set X}
  {μK : Measure K} {μQ : Measure Q} [SFinite μK] [SFinite μQ] {κ : K → Y} {Ψ : K × Q → X} {kc : X → K} {γ : K → ℝ}

end Abstract

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGw

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

section PartAGo1

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

def toM {s : ℕ} (A : Matrix (Fin s) (Fin s) ℂ) : Msq s := fun i j => A i j

def LUs (s : ℕ) : Set (Msq s × Msq s) := {p | IsLowerUni (Matrix.of p.1) ∧ IsUpperUni (Matrix.of p.2)}

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo1

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

section PartAGs2

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S

variable {s : ℕ} {ι : Type} [Fintype ι]

def emb (e : ι → Fin s × Fin s) (v : ι → ℂ) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => ∑ k, if e k = (i, j) then v k else 0

def phiR (e : ι → Fin s × Fin s) : ι ⊕ ι → Fin s × Fin s × Bool
  | Sum.inl k => ((e k).1, (e k).2, false)
  | Sum.inr k => ((e k).1, (e k).2, true)

theorem phiR_injective {e : ι → Fin s × Fin s} (he : Function.Injective e) : Function.Injective (phiR e) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp only [phiR, Prod.mk.injEq] at h <;>
    first
    | exact congrArg Sum.inl (he (Prod.ext h.1 h.2.1))
    | exact congrArg Sum.inr (he (Prod.ext h.1 h.2.1))
    | exact congrArg Sum.inl (he (Prod.ext h.1 h.2))
    | exact congrArg Sum.inr (he (Prod.ext h.1 h.2))
    | exact absurd h.2.2 (by decide)
    | simp at h

def JLin (e : ι → Fin s × Fin s) :
    EuclideanSpace ℝ (ι ⊕ ι) →ₗ[ℝ] EuclideanSpace ℝ (Fin s × Fin s × Bool) :=
  (EuclideanSpace.basisFun (ι ⊕ ι) ℝ).toBasis.constr ℝ (fun k => EuclideanSpace.single (phiR e k) (1 : ℝ))

theorem JLin_apply (e : ι → Fin s × Fin s) (y : EuclideanSpace ℝ (ι ⊕ ι)) (p : Fin s × Fin s × Bool) :
    JLin e y p = ∑ k, if phiR e k = p then y k else 0 := by
  classical
  rw [JLin, Module.Basis.constr_apply_fintype]
  simp [Pi.single_apply, eq_comm (a := p)]

def JIso {e : ι → Fin s × Fin s} (he : Function.Injective e) :
    EuclideanSpace ℝ (ι ⊕ ι) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s × Fin s × Bool) :=
  (JLin e).isometryOfOrthonormal (v := (EuclideanSpace.basisFun (ι ⊕ ι) ℝ).toBasis)
    (by rw [OrthonormalBasis.coe_toBasis]; exact (EuclideanSpace.basisFun (ι ⊕ ι) ℝ).orthonormal)
    (by
      have h : (JLin e) ∘ (EuclideanSpace.basisFun (ι ⊕ ι) ℝ).toBasis =
          (EuclideanSpace.basisFun (Fin s × Fin s × Bool) ℝ) ∘ phiR e := by
        funext k
        simp only [Function.comp, JLin]
        rw [Module.Basis.constr_basis]
        simp
      rw [h]
      exact (EuclideanSpace.basisFun (Fin s × Fin s × Bool) ℝ).orthonormal.comp _ (phiR_injective he))

def reals (v : ι → ℂ) : EuclideanSpace ℝ (ι ⊕ ι) :=
  WithLp.toLp 2 (Sum.elim (fun k => (v k).re) (fun k => (v k).im))

theorem reals_surjective : Function.Surjective (reals : (ι → ℂ) → EuclideanSpace ℝ (ι ⊕ ι)) := by
  intro y
  refine ⟨fun k => ⟨y (Sum.inl k), y (Sum.inr k)⟩, ?_⟩
  ext k
  rcases k with k | k <;> simp [reals]

theorem realify_emb (e : ι → Fin s × Fin s) (v : ι → ℂ) :
    (WithLp.equiv 2 _).symm (realifyFun (emb e v)) = JLin e (reals v) := by
  ext p
  obtain ⟨i, j, b⟩ := p
  rw [JLin_apply]
  cases b
  · simp only [Fintype.sum_sum_type, phiR, reals]
    simp [realifyFun, emb, Complex.re_sum, apply_ite Complex.re, Prod.ext_iff, and_assoc]
  · simp only [Fintype.sum_sum_type, phiR, reals]
    simp [realifyFun, emb, Complex.im_sum, apply_ite Complex.im, Prod.ext_iff, and_assoc]

theorem lieE_eq_range {e : ι → Fin s × Fin s} (he : Function.Injective e) {S : Set (Matrix (Fin s) (Fin s) ℂ)}
    (hS : lieOf S = Set.range (emb e)) : lieE S = LinearMap.range (JIso he).toLinearMap := by
  have h : (fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S =
      (LinearMap.range (JIso he).toLinearMap : Set (EuclideanSpace ℝ (Fin s × Fin s × Bool))) := by
    rw [hS]
    ext x
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨reals v, (realify_emb e v).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨v, rfl⟩ := reals_surjective y
      exact ⟨_, ⟨v, rfl⟩, realify_emb e v⟩
  rw [lieE, h, Submodule.span_eq]

def lieIso {e : ι → Fin s × Fin s} (he : Function.Injective e) {S : Set (Matrix (Fin s) (Fin s) ℂ)}
    (hS : lieOf S = Set.range (emb e)) : EuclideanSpace ℝ (ι ⊕ ι) ≃ₗᵢ[ℝ] lieE S :=
  (JIso he).equivRange.trans (LinearIsometryEquiv.ofEq _ _ (lieE_eq_range he hS).symm)

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGs2

section PartAGs3

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

def eL (d : ℕ) : UT d → Fin d × Fin d := Subtype.val

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGs3

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

end Formalism.MainNotions.InterlacingSignCuts.Gm

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

section PartALat

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FrobeniusOrbits

variable (D : D7)

theorem host_totallyComplex : NumberField.IsTotallyComplex D.host.E := by
  have := D.host.isCMField_hostE
  infer_instance

def plOf (v : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (plEmb D v)

theorem plOf_apply (v : D.what₂.Tau) (l : D.host.E) : plOf D v l = ‖plEmb D v l‖ := rfl

theorem plEmb_mem (v : D.what₂.Tau) : plEmb D v ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau v).2

theorem plEmb_injective : Function.Injective (plEmb D) := by
  intro v w h
  have h1 := (factEmb D.R D.host).1.1 h
  exact D.eTau.injective (Subtype.ext h1)

theorem plOf_bijective : Function.Bijective (plOf D) := by
  have hcm := D.host.der.cmType.1
  constructor
  · intro v w h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact plEmb_injective D h
    · exfalso
      have h1 := (hcm (plEmb D v)).1 (plEmb_mem D v)
      apply h1
      have : (starRingEnd ℂ).comp (plEmb D v) = plEmb D w := h
      rw [this]
      exact plEmb_mem D w
  · intro w
    by_cases hw : w.embedding ∈ D.host.cmType
    · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 w.embedding
      have hgP : g ∈ D.R.Psi := ((factEmb D.R D.host).2 g).1 (hg ▸ hw)
      refine ⟨D.eTau.symm ⟨g, hgP⟩, ?_⟩
      have : plEmb D (D.eTau.symm ⟨g, hgP⟩) = w.embedding := by
        unfold plEmb
        rw [Equiv.apply_symm_apply]
        exact hg
      unfold plOf
      rw [this, InfinitePlace.mk_embedding]
    · have hw' : (starRingEnd ℂ).comp w.embedding ∈ D.host.cmType := by
        by_contra hc
        exact hw ((hcm w.embedding).2 hc)
      obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((starRingEnd ℂ).comp w.embedding)
      have hgP : g ∈ D.R.Psi := ((factEmb D.R D.host).2 g).1 (hg ▸ hw')
      refine ⟨D.eTau.symm ⟨g, hgP⟩, ?_⟩
      have : plEmb D (D.eTau.symm ⟨g, hgP⟩) = ComplexEmbedding.conjugate w.embedding := by
        unfold plEmb
        rw [Equiv.apply_symm_apply]
        exact hg
      unfold plOf
      rw [this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem card_places : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective (plOf_bijective D)).symm

theorem f_pos : 0 < D.R.f := by
  rw [← card_places D]
  exact Fintype.card_pos

theorem prod_places (F : InfinitePlace D.host.E → ℝ) : ∏ w, F w = ∏ v, F (plOf D v) := by
  exact (Fintype.prod_bijective (plOf D) (plOf_bijective D) (fun v => F (plOf D v)) F (fun v => rfl)).symm

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

end

end PartALat

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

section PartASz

open NumberField Finset
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt.TA

attribute [local instance] Classical.propDecidable

section Sizes

variable (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (K : ℕ)

def szX (i : ℕ) (v : D.what₂.Tau) : ℝ := xSz D C1 C2 N (kaV D δ v) T T' (x v) i
def szL (b s : ℕ) (v : D.what₂.Tau) : ℝ := LamSz D C1 C2 N (kaV D δ v) T T' (x v) b s
def szP (b : ℕ) (v : D.what₂.Tau) : ℝ := LamPSz D C1 C2 N (kaV D δ v) T T' (x v) b

def szG (b s' : ℕ) (v : D.what₂.Tau) : ℝ := if s' = 1 then szX D C1 C2 N T T' δ x b v else szL D C1 C2 N T T' δ x b s' v

def thr3 (i s : ℕ) (v : D.what₂.Tau) : ℝ :=
  if i ≤ D.R.rS then szL D C1 C2 N T T' δ x (i - s + 1) (s + 1) v else 2 * szP D C1 C2 N T T' δ x (i - s + 1) v

def volB (b s' : ℕ) : ℝ := (∏ v, szG D C1 C2 N T T' δ x b s' v) ^ 2 / nrmHalf D (L.aaV b s') ^ 2

def bdB (C4 : ℝ) (i s : ℕ) : ℝ :=
  C4 ^ (D.R.f * s) * ∏ s' ∈ Ico 1 s, (Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s')

variable {D C1 C2 N T T' δ x L}

end Sizes

end Formalism.MainNotions.InterlacingSignCuts

end

end PartASz

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.InterlacingSignCuts
