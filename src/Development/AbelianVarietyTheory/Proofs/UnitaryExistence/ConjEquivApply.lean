import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.LevelHalf

open scoped Matrix nonZeroDivisors

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def conjEquiv (cm : CMData F E) : E ≃ₐ[F] E :=
  AlgEquiv.ofAlgHom cm.sig cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)

theorem conjEquiv_apply (cm : CMData F E) (x : E) : conjEquiv cm x = star x := rfl

def frameLat (V : HSpace E) : Submodule (𝓞 E) (Fin V.rank → E) :=
  V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 E))

theorem mem_frameLat (V : HSpace E) (v : Fin V.rank → E) :
    v ∈ frameLat V ↔ ∃ x ∈ V.L0, (fun i => V.frame.repr x i) = v := Iff.rfl

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end GlobalTheory.LevelHalf
