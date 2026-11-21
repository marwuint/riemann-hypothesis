import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFDOf
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def kfW (V : HSp D) (N : ℕ) : Subgroup (GA D V) := Subgroup.closure (levSet V N)

def LevGrp (V : HSp D) (N : ℕ) : Prop := ∀ k ∈ kfW V N, k ∈ levSet V N

theorem datHolds (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

end Formalism.L2.Pj
