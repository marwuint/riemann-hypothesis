import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonSummationDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsdFormConjRewrite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables

section PartDefs

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Defs

variable {D : D7} {k0 : ℕ} (G : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0)
  (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ) (χ : ℝ → ℝ)

def tau (i s : ℕ) (t : D.host.E) : D.what₂.Tau → ℂ := fun v => a i s v * plEmb D v t

def embA (i s : ℕ) : D.host.E →+ (D.what₂.Tau → ℂ) where
  toFun := tau a i s
  map_zero' := by funext v; simp [tau]
  map_add' := fun x y => by funext v; simp [tau, mul_add]

def laC (L : LatticeDataWithDual D) (i s : ℕ) : AddSubgroup (D.what₂.Tau → ℂ) := (L.La i s).toAddSubgroup.map (embA a i s)

def sgm (δ : D.host.E) (i s : ℕ) (l : D.host.E) : D.what₂.Tau → ℂ :=
  fun v => 2 * (Real.pi : ℂ) * Complex.I * plEmb D v (l / δ) / a i s v

def aDual (δ : D.host.E) (i s : ℕ) : D.what₂.Tau → ℂ :=
  fun v => 2 * (Real.pi : ℂ) * Complex.I / (plEmb D v δ * a i s v)

end Defs

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs

section PartDefs2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

structure Mod (D : D7) {k0 : ℕ} (X : GramWordSpace.Dat D k0) (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ)
    (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D)
    (κL : ℕ → ℕ → ℝ) : Prop where
  std : X.Std Ks E₀ Eg
  δ_ne : δ ≠ 0
  a_ne : ∀ i s v, a i s v ≠ 0
  cb_pos : ∀ i s, 0 < cb i s
  lowerConstantNonneg : 0 ≤ c0
  brk_pos : ∀ w, X.admitted w → 0 < X.brk w
  xi_nn : ∀ i v, 0 ≤ X.xi E₁ E₂ Ks i v
  blockSizeNonneg : ∀ j0 s v, 0 ≤ GramWordSpace.blockLiftThreshold X E₁ E₂ Ks j0 s v
  thr1 : ∀ i v, 1 ≤ i → i ≤ D.R.rS + 1 →
    X.xi E₁ E₂ Ks i v * ‖a i 1 v‖ ≤ kaV D δ v * szX D C C (Nlet D Ks) T T' δ x i v
  thr3 : ∀ i s v, 1 ≤ s → s ≤ i → i ≤ D.R.rS + 1 → ¬ (i = D.R.rS + 1 ∧ s = 1) →
    GramWordSpace.blockLiftThreshold X E₁ E₂ Ks (i - s) s v * ‖a (i - s + 1) s v‖ ≤ thr3 D C C (Nlet D Ks) T T' δ x i s v
  lat : ∀ b s, IsBlockSL2Embedding D b s → GramWordSpace.IsLat D (laC a L b s) (κL b s)
  dual : ∀ b s, IsBlockSL2Embedding D b s → ∀ σ ∈ GramWordSpace.dualS D (laC a L b s), ∃ l ∈ dualPsi D δ (L.La b s), σ = sgm a δ b s l
  dualV : ∀ b s, IsBlockSL2Embedding D b s → dualPsi D δ (L.La b s) ⊆ (L.aaV b s : Set D.host.E)
  cb1 : ∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → cb i 1 = κL i 1
  blockProductBound : ∀ b s, 2 ≤ s → IsBlockSL2Embedding D b s →
    ∏ v, X.abelian₂ E₁ E₂ Ks s b v ≤ Real.sqrt (GramWordSpace.scNorm D (aDual a δ b s) (L.aaV b s))
  blockSL2Embedding_bound : ∀ b s, 2 ≤ s → IsBlockSL2Embedding D b s →
    cb b s / κL b s * (E₃ ^ (D.R.f * s) * ∏ s' ∈ Finset.Ico 1 s, ∏ v, X.LamG E₁ E₂ Ks s' b v ^ 2) ≤
      bdB D C C (Nlet D Ks) T T' δ x L C4 (b + s - 1) s

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs2

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

section PartPoPi

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Maps

open scoped FourierTransform

variable {ι : Type} [Fintype ι]

abbrev VV (ι : Type) [Fintype ι] := EuclideanSpace ℝ (ι ⊕ ι)

def piL (k : ι) : VV ι →ₗ[ℝ] ℂ where
  toFun y := ⟨y (Sum.inl k), y (Sum.inr k)⟩
  map_add' a b := by apply Complex.ext <;> simp
  map_smul' c a := by apply Complex.ext <;> simp

def piC (k : ι) : VV ι →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (piL k)

end Maps

end Formalism.MainNotions.BlockEstimateWords

end

end PartPoPi

section PartLat1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

open NumberField

theorem trace_places {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ a)
      (fun σ => σ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ a)] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have hq : (algebraMap ℚ ℂ (Algebra.trace ℚ K a)).re = ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
    simp
  rw [hq] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.re_sum]
  have hfib : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hm := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hm
    rcases hm with rfl | hc
    · rfl
    · rw [← hc, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two]
  simp

theorem trace_tau (D : D7) (x : D.host.E) :
    ((Algebra.trace ℚ D.host.E x : ℚ) : ℝ) = ∑ v, 2 * (plEmb D v x).re := by
  have := host_totallyComplex D
  rw [trace_places x]
  refine (Fintype.sum_bijective (plOf D) (plOf_bijective D) _ _ fun v => ?_).symm
  rcases InfinitePlace.embedding_mk_eq (plEmb D v) with h | h
  · show _ = 2 * ((InfinitePlace.mk (plEmb D v)).embedding x).re
    rw [h]
  · show _ = 2 * ((InfinitePlace.mk (plEmb D v)).embedding x).re
    rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

section Scl

variable {ι : Type} [Fintype ι]

def scl (c : ι → ℂ) : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
  LinearMap.pi fun v => (Algebra.lmul ℝ ℂ (c v)) ∘ₗ LinearMap.proj v

theorem scl_apply (c : ι → ℂ) (t : ι → ℂ) (v : ι) : scl c t v = c v * t v := by
  rfl

end Scl

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat1

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

section PartLat2b

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Geo

open NumberField

variable (D : D7)

instance hostFieldTotallyComplex : NumberField.IsTotallyComplex D.host.E := host_totallyComplex D

theorem place_is_complex (v : D.what₂.Tau) : (plOf D v).IsComplex := NumberField.IsTotallyComplex.isComplex _

def l2Pl : D.what₂.Tau ≃ {w : InfinitePlace D.host.E // w.IsComplex} :=
  Equiv.ofBijective (fun v => ⟨plOf D v, place_is_complex D v⟩) (by
    constructor
    · intro v w h
      exact (plOf_bijective D).1 (congrArg Subtype.val h)
    · intro w
      obtain ⟨v, hv⟩ := (plOf_bijective D).2 w.1
      exact ⟨v, Subtype.ext hv⟩)

instance no_real_places : IsEmpty {w : InfinitePlace D.host.E // w.IsReal} :=
  ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (NumberField.IsTotallyComplex.isComplex w.1)) w.2⟩

end Geo

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2b

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

section PartDefs3

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

def sclL (av : ℕ → ℕ → ℂ) : ℕ → List (ℂ × ℕ) → List (ℂ × ℕ)
  | _, [] => []
  | o, (t, s) :: bs => (av (o + 1) s * t, s) :: sclL av (o + s) bs

def okL (r : ℕ) (T T' : ℝ) (o s : ℕ) (t : ℂ) : Prop := t ≠ 0 ∧ (s = 1 → o = r → T * T' < Complex.normSq t)

def wLoc (k r : ℕ) (T T' : ℝ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | o, (t, s) :: bs =>
    (if okL r T T' o s t then Real.sqrt (ptWeightFrom k r T T' o [(t, s)]) else 0) * wLoc k r T T' (o + s) bs

def cblk (κ : ℝ) (i s : ℕ) : ℝ := (κ ^ (s * (s - 1)))⁻¹ * ∏ l ∈ Finset.Ico i (i + s), κ ^ (4 * (l - 1))

def ccL (κ : ℝ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | o, (_, s) :: bs => Real.sqrt (cblk κ (o + 1) s) * ccL κ (o + s) bs

structure LocFrame (D : D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS) (B : LocBessel D.R.k D.R.rS)
    (f : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) where
  B' : LocBessel (k0 + 1) D.R.rS
  f' : GramWordSpace.GFn B'
  μ' : GramWordSpace.Sec k0
  av : ℕ → ℕ → ℂ
  A : ℝ
  hc : B'.c = cStd
  hε : ∀ i, B'.ε i = B.ε (Fin.cast (by omega) i)
  hlam : ∀ i, B'.lam i = B.lam (Fin.cast (by omega) i)
  hu : ∀ i, B'.u i = B.u (Fin.cast hk i)
  hu' : ∀ i, B'.u' i = B.u' (Fin.cast hk i)
  hT : Tz (k0 + 1) D.R.rS B'.z = (‖B.c‖ / 2) ^ (2 * D.R.rS) * Tz D.R.k D.R.rS B.z
  hT' : Tz (k0 + 1) D.R.rS B'.z' = (‖B.c‖ / 2) ^ (2 * D.R.rS) * Tz D.R.k D.R.rS B.z'
  hsec : IsSection (k0 + 1) D.R.rS B'.z B'.z' μ'
  hf : UnitaryLevelOperators.IsKFinCoefT B'.σ f'
  hav : ∀ i s, ‖av i s‖ = (‖B.c‖ / 2) ^ (2 * i + s - 3)
  hA : 0 < A
  val : ∀ γ γ' : Point ℂ (D.R.rS + 1),
    ((Real.sqrt (ptWeightFrom D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') 0 γ.1) *
        Real.sqrt (ptWeightFrom D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') 0 γ'.1) : ℝ) : ℂ) *
      hsInner ((BlockEstimateTheorem.vmOf D hk G).V B f γ.1) ((BlockEstimateTheorem.vmOf D hk G).V B f γ'.1) =
    ((A * (ccL (‖B.c‖ / 2) 0 γ.1 * ccL (‖B.c‖ / 2) 0 γ'.1) *
        (wLoc (k0 + 1) D.R.rS (Tz (k0 + 1) D.R.rS B'.z) (Tz (k0 + 1) D.R.rS B'.z') 0 (sclL av 0 γ.1) *
          wLoc (k0 + 1) D.R.rS (Tz (k0 + 1) D.R.rS B'.z) (Tz (k0 + 1) D.R.rS B'.z') 0 (sclL av 0 γ'.1)) : ℝ) : ℂ) *
      hsInner (G.V B' f' (sclL av 0 γ.1)) (G.V B' f' (sclL av 0 γ'.1))
  energy : ENNReal.ofReal (A * (B'.beta μ' f' f').re) ≤
    ∫⁻ p : (Fin D.R.rS → ℂ) × ℂ, ENNReal.ofReal (bcWeight D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') p *
      hsNormSq (B.J f (bigCell D.R.k D.R.rS p.1 (μsec p.2))))

structure XTie {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (x : D.what₂.Tau → LocalDataRealPlace D) (T T' : ℝ) (kap : D.what₂.Tau → ℝ) : Prop where
  hT : ∀ v, X.T v = kap v ^ (2 * D.R.rS) * T
  hT' : ∀ v, X.T' v = kap v ^ (2 * D.R.rS) * T'
  lam : ∀ v, (X.loc v).lam = (x v).lam
  u : ∀ v, (X.loc v).u = (x v).u
  u' : ∀ v, (X.loc v).u' = (x v).u'
  a : ∀ v, X.a v = (x v).a
  b : ∀ v, X.b v = (x v).b
  a1 : ∀ v, X.a1 v = (x v).a1
  b1 : ∀ v, X.b1 v = (x v).b1

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs3

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords

namespace Formalism.MainNotions.BlockEstimateWords

end Formalism.MainNotions.BlockEstimateWords
