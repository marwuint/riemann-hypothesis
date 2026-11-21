import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFrameOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamFramedOfPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatFramedOfGramPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColsInIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHtNumsOfKerSideLastSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeWordLocalConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodBoundLastLog
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonnegSubOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRowsTop

open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum GlobalTheory.LastPeriod in

theorem periodFun_le (hL : LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)) (s : X.K →+* ℂ)
    (ψ : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m))
    (F : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K W.sgTrue) :
    ‖s (PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) u ψ F)‖ ^ 2 ≤
      Real.exp (lastLog W u) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) (GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u) s ψ *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) s F := by
  have hT : (0 : ℝ) < (Pr.T u : ℝ) := Nat.cast_pos.2 (hPr.T_prime u).pos
  have ht : ∀ τ, star (s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E)))) * s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E))) =
      ((Pr.T u : ℝ) : ℂ) := fun τ => by
    have h1 := hX.conjE (s.comp (X.emb τ)) (star ((Pr.piT u : 𝓞 X.E) : X.E))
    rw [star_star, RingHom.comp_apply, RingHom.comp_apply, starRingEnd_apply] at h1
    have h2 : ((Pr.piT u : 𝓞 X.E) : X.E) * star ((Pr.piT u : 𝓞 X.E) : X.E) = (Pr.T u : X.E) := by
      have := congrArg (fun z : 𝓞 X.E => (z : X.E)) (hPr.piT_norm u)
      simp only [map_mul, map_natCast] at this
      exact this
    rw [← h1, ← map_mul, ← map_mul, h2]
    simp
  have hB := coefOpLe_brAt hL s (N_m_succ R) (W.lamTrue u R.m) W.sgTrue hI hS _ hT _ ht
  set hM := mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P
  set hE := GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u
  let _ := hM.fintypeCl
  have h := sum_pair_le s _ _ _ _ hB ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt
    (fun c => ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
    (fun c => F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
  have e0 : PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P hM u ψ F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : X.K)⁻¹ *
        pairBK W.sgTrue (brC W u (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)))
          (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold PtilFF GSD.csOf
    exact (LinearMap.congr_fun (LinearMap.sum_apply _ _ _) _).trans (LinearMap.sum_apply _ _ _)
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) hE s ψ =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s (W.lamTrue u R.m) (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (re_inv_mul _ _).trans
      (congrArg₂ (· * ·) rfl ((gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ (W.lamTrue u R.m) s).2 _))
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) hM s F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s W.sgTrue (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hg := (gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ W.sgTrue s).2
    simp only [pairVr_one_eq, pairK_one_basis] at hg
    refine (re_inv_mul _ _).trans (congrArg₂ (· * ·) rfl (Eq.trans ?_ (hg _)))
    unfold GSD.pairAt
    rw [row_gramV]
    rfl
  rw [e0, e1, e2]
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) ?_)
  · rw [lastLog, Real.exp_add, mul_comm (-_ : ℝ), ← Real.rpow_def_of_pos hT, ← Int.cast_neg, Real.rpow_intCast]
    exact mul_le_mul_of_nonneg_left (Real.le_exp_log _) (by positivity)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)

theorem period_le (hL : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks}
    (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg) (hmu : mu = 1)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hP : (mtildeGSD W Ch sel mu P).Ok) (hE : (evGSD W Ch sel mu P u).Ok) (v : InfinitePlace X.K)
    (ψ : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m)) (F : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K W.sgTrue) :
    v (PtilFF W Ch sel mu P hP u ψ F) ^ 2 ≤
      Real.exp (lastLog W u) * ((evGSD W Ch sel mu P u).ipAt hE v ψ ψ).re * ((mtildeGSD W Ch sel mu P).ipAt hP v F F).re := by
  subst hmu
  have h := periodFun_le hL hX hPr W Ch sel Sg P u hI hS v.embedding ψ F
  rw [InfinitePlace.norm_embedding_eq] at h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt, InfinitePlace.mk_embedding] at h
  exact h

theorem ipAt_nonneg_of_datFramed {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {h : S.Ok} (hS : DatFramed S h)
    (v : InfinitePlace K) (ψ : S.EqFun) : 0 ≤ (S.ipAt h v ψ ψ).re := by
  obtain ⟨n, e, X, -, hX⟩ := hS
  obtain ⟨y, rfl⟩ := e.surjective ψ
  rw [← hX v y, Complex.ofReal_re]
  positivity

end GlobalTheory.ColRowsTop
