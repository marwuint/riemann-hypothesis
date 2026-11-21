import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg.StdFrame

theorem castGL_rfl {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  ext i j
  simp [castGL]

end GlobalTheory.Mem.R3.LiftBrg.StdFrame

namespace GlobalTheory.Mem.R3.LiftBrg

end GlobalTheory.Mem.R3.LiftBrg
