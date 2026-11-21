import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SupremumLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral

noncomputable section

namespace GlobalTheory.GoodLat.Road

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice

abbrev kapRows (D : D7) : Rows.Data D.R :=
  { D.what₂ with
    kaBig := fun j τ i => (DV.aPlusQ_int D j τ i).choose
    kaSmall := fun j τ c => -(DV.aMinusQ_int D j τ c).choose }

set_option maxHeartbeats 4000000 in

def kapRec (D : D7) : D7 :=
  { D with
    what₂ := kapRows D
    nd := { D.nd with }
    ntw := { D.ntw with }
    naut := { D.naut with }
    nbc := { D.nbc with }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with }
    nth := { D.nth with } }

def kapCore {D : D7} (T : Core D) : Core (kapRec D) :=
  { T with Q := { T.Q with } }

set_option maxHeartbeats 1000000 in
theorem supLatticeFullAt_kapCore {D : D7} (T : Core D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    SupLatticeFullAt (kapCore T) j a n ↔ SupLatticeFullAt T j a n := Iff.rfl

end GlobalTheory.GoodLat.Road
