import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Formalism.UG.P

namespace GlobalTheory.MeasTupleEq

theorem map_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  classical
  let M : Matrix (Fin n) (Fin n) O := fun a b =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix (Fin n) (Fin n) _) a b)
  have hM : M.map (IsLocalRing.residue O) = (g : Matrix (Fin n) (Fin n) _) := by
    ext a b
    simp only [M]
    exact Function.surjInv_eq _ _
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (IsLocalRing.residue O M.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det g).isUnit
    exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h1
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hdet, Units.ext ?_⟩
  exact hM

variable {D : D7} {X : ThetaX D}

end GlobalTheory.MeasTupleEq

end
