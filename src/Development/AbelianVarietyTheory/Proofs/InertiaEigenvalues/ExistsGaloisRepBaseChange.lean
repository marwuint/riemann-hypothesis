import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightLocalisationRegularAlgebraic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.GalIsoBC

theorem lpTw_lpZero (D : D7) (w : PlE D.host) (s : ℝ) : D.naut.lpTw (D.naut.lpZero w) s = D.naut.lpZero w := by
  have hu : D.naut.unr (D.naut.lpTw (D.naut.lpZero w) s) := (D.naut.unr_tw _ s).2 (D.naut.lpZero_unr w)
  have e3 : D.naut.frobEig (D.naut.lpTw (D.naut.lpZero w) s) = D.naut.frobEig (D.naut.lpZero w) := by
    rw [D.naut.frobEig_tw _ s (D.naut.lpZero_unr w), D.naut.frobEig_zero]; simp
  rw [D.naut.unr_eq_lpUnr _ hu, e3, ← D.naut.unr_eq_lpUnr _ (D.naut.lpZero_unr w)]

theorem lpTw_foldr (D : D7) (w : PlE D.host) {β : Type*} (f : β → D.naut.LP w) (s : ℝ) :
    ∀ L : List β, D.naut.lpTw (L.foldr (fun x acc => D.naut.lpSum (f x) acc) (D.naut.lpZero w)) s =
      L.foldr (fun x acc => D.naut.lpSum (D.naut.lpTw (f x) s) acc) (D.naut.lpZero w)
  | [] => lpTw_lpZero D w s
  | x :: L => by
      simp only [List.foldr_cons]
      rw [D.naut.lpTw_sum, lpTw_foldr D w f s L]

theorem map_list_sum {α γ : Type*} (h : α → γ) :
    ∀ L : List (Multiset α), L.sum.map h = (L.map fun x => x.map h).sum
  | [] => by simp
  | x :: L => by simp [Multiset.map_add, map_list_sum h L]

theorem le_list_sum {α : Type*} {x : Multiset α} : ∀ {L : List (Multiset α)}, x ∈ L → x ≤ L.sum
  | [], hx => by simp at hx
  | y :: L, hx => by
      rw [List.sum_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Multiset.le_add_right _ _
      · exact le_trans (le_list_sum hx) (Multiset.le_add_left _ _)

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

theorem flatMap_single {γ : Type*} (f : ℕ → γ) : ∀ l : List ℕ, List.flatMap (fun a => [f a]) l = l.map f
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatMap_single f l]

theorem spehLoc_eq (D : D7) (p : Formalism.BasicNotions.Part D.naut.CG) (w : PlE D.host) :
    spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (k : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ))) acc) (D.naut.lpZero w) := by
  unfold spehLoc
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℝ)), List.foldr_map]

theorem isoInf_eq (D : D7) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut Pa τ = (Pa.map fun p => ((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).sum := by
  unfold isoInf
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℂ)), List.map_map]
  rfl

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

end GlobalTheory.GalIsoBC
