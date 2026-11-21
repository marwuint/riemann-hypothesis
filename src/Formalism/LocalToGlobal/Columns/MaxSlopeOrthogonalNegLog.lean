import Mathlib
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN

section F3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable [IsTotallyComplex K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem slope_line_le_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  have hf : 0 < nPl K := Fintype.card_pos
  have hfR : (0 : ℝ) < (nPl K : ℝ) := by exact_mod_cast hf
  obtain ⟨-, hmu, -⟩ := size_maximal_slope K V ι b X hX L hLfg hL0
  have hpos : 0 < ht b X L := (place_lattice_structure K V ι b X hX L hLfg).2.2
  have hli : LinearIndependent K (fun _ : Fin 1 => x) := LinearIndependent.of_subsingleton (0 : Fin 1) hx
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hg := (height_gram_determinant K V ι b X hX 1 (fun _ : Fin 1 => x) hli).1
  rw [hrange] at hg
  have hht : c ^ (nPl K) ≤ ht b X L := by
    rw [hL, hg]
    have h1 : ∀ v : InfinitePlace K, c ≤ (gramPl b X v (fun _ : Fin 1 => x)).det.re := by
      intro v
      rw [Matrix.det_fin_one]
      simp only [gramPl, Matrix.of_apply]
      rw [Formalism.ExtensionFiltration.majAt_self_re]
      exact hn v
    calc c ^ (nPl K) = ∏ _v : InfinitePlace K, c := by rw [Finset.prod_const, Finset.card_univ]; rfl
      _ ≤ ∏ v, (gramPl b X v (fun _ : Fin 1 => x)).det.re := Finset.prod_le_prod (fun v _ => hc.le) (fun v _ => h1 v)
  have hlog : (nPl K : ℝ) * Real.log c ≤ Real.log (ht b X L) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hht
  rw [hmu]
  unfold size
  rw [Real.log_rpow hpos, hrk]
  have : Real.log c / 2 ≤ (1 : ℝ) / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L) := by
    rw [Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

theorem max_slope_line_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muMaxDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  have : Module.Finite K V := Module.Finite.of_basis b
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  refine Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le b X hL0 fun Q hQ hQ0 => ?_
  have h1 : rkK (K := K) Q ≤ 1 := by
    rw [← hrk]
    exact Submodule.finrank_mono (Submodule.span_mono hQ)
  have h2 : 0 < rkK (K := K) Q := Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hQ0
  have hrkQ : rkK (K := K) Q = rkK (K := K) L := by omega
  have hi := (Formalism.LFunctionChainParameters.LLcv.index_slope_formula K V ι b X hX L Q hLfg hQ hQ0 hrkQ).1
  have hl : 0 ≤ Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := Real.log_natCast_nonneg _
  have hn' : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : 0 ≤ 2 * Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) / ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by
    rw [hrk]
    positivity
  have := slope_line_le_neg_log b X hX x hx c hc hn
  rw [hi]
  linarith

end F3

end Formalism.L2.Col
