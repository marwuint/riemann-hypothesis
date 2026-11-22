import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemUQptsStarCIff

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.VF : Type := D.VQ

instance Datum.acgVF : AddCommGroup D.VF := inferInstanceAs (AddCommGroup D.VQ)

instance Datum.modQVF : Module ℚ D.VF := inferInstanceAs (Module ℚ D.VQ)

instance Datum.modFVF : Module D.F D.VF :=
  Module.compHom D.VQ ((D.endO.val : D.endO →ₐ[ℚ] Module.End ℚ D.VQ).toRingHom.comp D.actF.toRingHom)

theorem Datum.smul_VF (x : D.F) (v : D.VF) :
    x • v = (((D.actF x : D.endO) : Module.End ℚ D.VQ) (v : D.VQ) : D.VF) := rfl

instance Datum.towerVF : IsScalarTower ℚ D.F D.VF :=
  ⟨fun q x v => by
    show ((D.actF (q • x) : D.endO) : Module.End ℚ D.VQ) v = q • ((D.actF x : D.endO) : Module.End ℚ D.VQ) v
    rw [map_smul]; rfl⟩

def Datum.endFL (g : D.endO) : Module.End D.F D.VF where
  toFun v := ((g : Module.End ℚ D.VQ) v : D.VQ)
  map_add' v w := map_add (g : Module.End ℚ D.VQ) v w
  map_smul' x v := by
    show (g : Module.End ℚ D.VQ) (((D.actF x : D.endO) : Module.End ℚ D.VQ) v) =
      ((D.actF x : D.endO) : Module.End ℚ D.VQ) ((g : Module.End ℚ D.VQ) v)
    have := congrArg (fun k : D.endO => (k : Module.End ℚ D.VQ) v) (D.actF_comm x g)
    exact this.symm

def Datum.endF : D.endO →+* Module.End D.F D.VF where
  toFun := D.endFL
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

instance Datum.algFw (τ : D.F →+* PadicAlgCl p) : Algebra D.F (GlobalTheory.LKTrip.FwOf τ) := (GlobalTheory.LKTrip.embOf τ).toAlgebra

abbrev Datum.VL (τ : D.F →+* PadicAlgCl p) : Type := GlobalTheory.LKTrip.FwOf τ ⊗[D.F] D.VF

def Datum.endL (τ : D.F →+* PadicAlgCl p) : D.endO →+* Module.End (GlobalTheory.LKTrip.FwOf τ) (D.VL τ) :=
  (Module.End.baseChangeHom D.F (GlobalTheory.LKTrip.FwOf τ) D.VF).toRingHom.comp D.endF

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

theorem Datum.finrank_VF : Module.finrank D.F D.VF = D.m * D.n := by
  have h1 : Module.finrank ℚ D.VF = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa; haveI := D.finLa
    show Module.finrank ℚ (ℚ ⊗[ℤ] D.La) = _
    rw [Module.finrank_baseChange, D.rankLa]
  haveI : FiniteDimensional ℚ D.VF := D.finVQ
  haveI : FiniteDimensional D.F D.VF := Module.Finite.of_restrictScalars_finite ℚ D.F D.VF
  rw [← Module.finrank_mul_finrank ℚ D.F D.VF, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

instance Datum.finVF : FiniteDimensional D.F D.VF :=
  haveI : FiniteDimensional ℚ D.VF := D.finVQ
  Module.Finite.of_restrictScalars_finite ℚ D.F D.VF

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MatUnit

end GlobalTheory.UPel.HT.MatUnit
