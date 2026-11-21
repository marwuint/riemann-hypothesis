import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitBCOfGalIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentEigenvalueSumFormula

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MuBlock

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem frobEig_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (f : ℝ → ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) ∧
    A.frobEig (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) =
      (L.map fun k => (A.frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((f k : ℝ) : ℂ))).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons k L ih =>
    have hk := (A.unr_tw a (f k)).2 ha
    refine ⟨(A.unr_sum _ _).2 ⟨hk, ih.1⟩, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [A.frobEig_sum _ _ hk ih.1, A.frobEig_tw a _ ha, ih.2]

theorem frobEig_spehLoc (p : Part A.CG) (w : PlE H) (h : A.unr (A.locG p.π w)) :
    A.unr (spehLoc N A p w) ∧ A.frobEig (spehLoc N A p w) =
      ((List.range p.d).map fun k => (A.frobEig (A.locG p.π w)).map
        (· * ((normV w : ℕ) : ℂ) ^ (((((p.d : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum :=
  frobEig_foldr N A _ h (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) _

theorem frobEig_isoLoc (Pa : List (Part A.CG)) (w : PlE H) (h : ∀ p ∈ Pa, A.unr (A.locG p.π w)) :
    A.unr (isoLoc N A Pa w) ∧ A.frobEig (isoLoc N A Pa w) =
      (Pa.map fun p => ((List.range p.d).map fun k => (A.frobEig (A.locG p.π w)).map
        (· * ((normV w : ℕ) : ℂ) ^ (((((p.d : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum := by
  induction Pa with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons p Pa ih =>
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := frobEig_spehLoc N A p w (h p (List.mem_cons_self ..))
    refine ⟨(A.unr_sum _ _).2 ⟨hp.1, ih'.1⟩, ?_⟩
    change A.frobEig (A.lpSum (spehLoc N A p w) (isoLoc N A Pa w)) = _
    rw [A.frobEig_sum _ _ hp.1 ih'.1, hp.2, ih'.2]
    simp only [List.map_cons, List.sum_cons]

theorem frobEig_eq_single {w : PlE H} (a : A.LP w) (hu : A.unr a) (hd : A.lpDim a = 1) :
    ∃ c, A.frobEig a = {c} :=
  Multiset.card_eq_one.1 (by rw [A.frobEig_card a hu, hd])

theorem absNorm_eq_normV (w : PlE H) : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem exists_split_not_mem (hC : ∀ Sg : Set (PlE H), Sg.Finite →
    closure {σ : G H.E N.Om | ∃ w ∉ Sg, IsSplitPl H w ∧ ∃ B : ValuationSubring N.Om,
      IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ} = Set.univ)
    (S : Set (PlE H)) (hS : S.Finite) : ∃ w ∉ S, IsSplitPl H w := by
  by_contra hn
  push_neg at hn
  have h := hC S hS
  have he : {σ : G H.E N.Om | ∃ w ∉ S, IsSplitPl H w ∧ ∃ B : ValuationSubring N.Om,
      IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ} = ∅ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨w, hw, hs, -⟩
    exact hn w hw hs
  rw [he, closure_empty] at h
  exact Set.empty_ne_univ h

end GlobalTheory.MuBlock

namespace GlobalTheory.MuBlock

end GlobalTheory.MuBlock

namespace GlobalTheory.MuBlock

end GlobalTheory.MuBlock
