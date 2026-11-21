import Formalism.SharpRestriction.InertJacobiLevels.ExtraKer
import Formalism.SharpRestriction.InertJacobiLevels.ExtraVal
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

structure PlEmb (D : D7) where
  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_spec : ∀ w x, ∃ hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ, iL w x = lam w ⟨D.what₂.embLL x, hx⟩
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

def plEmb (D : D7) : PlEmb D where
  lam := fun w => (Examples₂.exists_placeEmb D w).choose
  iL := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose
  iL_spec := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose_spec.1
  iL_int := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose_spec.2

def entZero (D : D7) (Dx : DivX D) (Tw : TwForms D) (PE : PlEmb D) [∀ u μ i, IsEmpty ((D.chTw u μ).Y i)]
    [∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))] : KerEnt D Dx Tw where
  lam := PE.lam
  iL := PE.iL
  iL_lam := fun w x => by
    obtain ⟨hx, h⟩ := PE.iL_spec w x
    unfold lamV
    rw [dif_pos hx, h]
  iL_int := PE.iL_int
  Th := fun _ _ _ _ _ _ => 0
  VQ := fun _ _ _ _ => PUnit
  ev := fun _ _ _ _ => 0
  ev_inj := fun _ _ _ _ _ _ _ => rfl
  prS := fun _ _ _ _ _ => 0
  prT := fun _ _ _ _ _ => 0
  prT_val := fun _ _ _ _ _ _ c' => isEmptyElim c'
  lat_S := fun u μ w _ i _ φ =>
    ⟨fun _ => ⟨by
        rw [show φ = 0 from funext fun _ => funext fun y => isEmptyElim y]
        exact Submodule.zero_mem _, fun c => ⟨0, funext fun y => isEmptyElim y, fun _ => by simp⟩⟩,
      fun _ => ⟨0, Submodule.zero_mem _, funext fun _ => funext fun y => isEmptyElim y⟩⟩
  levelFree_lattice_condition := fun u μ w _ i _ φ =>
    ⟨fun _ => ⟨by
        rw [show φ = 0 from funext fun _ => funext fun y => isEmptyElim y]
        exact Submodule.zero_mem _, fun c' => isEmptyElim c'⟩,
      fun _ => ⟨0, Submodule.zero_mem _, funext fun _ => funext fun y => isEmptyElim y⟩⟩
  un := fun _ _ _ _ _ _ => 1
  un_ne := fun _ _ _ _ _ _ => one_ne_zero
  kform := fun _ _ _ _ _ _ _ c' => isEmptyElim c'

theorem entZero_lam (D : D7) (Dx : DivX D) (Tw : TwForms D) (PE : PlEmb D) [∀ u μ i, IsEmpty ((D.chTw u μ).Y i)]
    [∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))] (w) : (entZero D Dx Tw PE).lam w = PE.lam w := rfl

end Formalism.MainNotions.Inhab

end
