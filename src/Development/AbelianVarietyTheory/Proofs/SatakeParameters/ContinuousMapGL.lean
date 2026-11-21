import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.ContraPair
open GlobalTheory.ThetaPull (cFin pInf_conjAd pFin_conjAd conjAd_conjAd continuous_conjAd)
open scoped ContDiff

namespace GlobalTheory.BarPull

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

theorem map_map_comm (p : R →+* S) (c : R →+* R) (c' : S →+* S) (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map p g) := by
  ext i j
  exact h _

theorem continuous_mapGL [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R) (h : Continuous c) :
    Continuous (GeneralLinearGroup.map (n := Fin a) c) :=
  Continuous.units_map _ (continuous_matrix fun i j => h.comp (continuous_id.matrix_elem i j))

theorem map_unip {r : ℕ} (c : R →+* R) (x : BlockIx a r → R) :
    GeneralLinearGroup.map c (unip x) = unip fun p => c (x p) := by
  ext i j
  change c ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM fun p => c (x p) : Matrix (Fin a) (Fin a) R) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

omit [IsCMField E] in

def barL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => star (X i j)
      map_add' := fun X Y => by funext i j; simp
      map_smul' := fun t X => by funext i j; simp }

variable (E a) in

def barA : GA E a →* GA E a := GeneralLinearGroup.map (conjAd E)

theorem barA_barA (g : GA E a) : barA E a (barA E a g) = g := by
  ext i j : 2
  exact conjAd_conjAd _

theorem barA_infGL (y : GL (Fin a) (Cinf E)) :
    barA E a (infGL E a y) = infGL E a (GeneralLinearGroup.map (starRingEnd (Cinf E)) y) :=
  ga_ext (by rw [barA, map_map_comm _ _ _ pInf_conjAd, pInf_infGL, pInf_infGL])
    (by rw [barA, map_map_comm _ _ _ pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

theorem chart_bar (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (barA E a g)) g x = chart φ (barA E a g) (barL x) ∧ barL x ∈ invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [show barL (toL u.val) = toL (GeneralLinearGroup.map (starRingEnd (Cinf E)) u).val from rfl,
    chart_val, chart_val, map_mul, barA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem bar_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun g => φ (barA E a g)) ∈ Sm E a := fun g =>
  ((hφ (barA E a g)).comp (barL (E := E) (a := a)).contDiff.contDiffOn
    fun _ hx => (chart_bar φ g hx).2).congr fun _ hx => (chart_bar φ g hx).1

variable (E a) in

def pull : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun g => φ.1 (barA E a g), bar_mem_Sm φ.2⟩
  invFun φ := ⟨fun g => φ.1 (barA E a g), bar_mem_Sm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (barA_barA g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (barA_barA g)

theorem pull_apply (φ : Sm E a) (g : GA E a) : (pull E a φ).1 g = φ.1 (barA E a g) := rfl

end GlobalTheory.BarPull

end
