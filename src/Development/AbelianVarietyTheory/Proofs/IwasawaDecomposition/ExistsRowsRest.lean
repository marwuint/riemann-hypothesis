import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerProductPositiveDefinite

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.SmallRows

def RamSp {B : Base} (C : Cols B) (u : B.Word) : Type := (C.mem u).A.Mram

instance {B : Base} (C : Cols B) (u : B.Word) : AddCommGroup (RamSp C u) :=
  inferInstanceAs (AddCommGroup (C.mem u).A.Mram)
instance {B : Base} (C : Cols B) (u : B.Word) : Module ℂ (RamSp C u) :=
  inferInstanceAs (Module ℂ (C.mem u).A.Mram)
instance {B : Base} (C : Cols B) (u : B.Word) : FiniteDimensional ℂ (RamSp C u) :=
  haveI := (C.mem u).A.Mu0_fd
  Submodule.finiteDimensional_of_le (S₁ := (C.mem u).A.Mram) (S₂ := (C.mem u).A.Mu0) inf_le_left

end GlobalTheory.Mem.SmallRows

end
