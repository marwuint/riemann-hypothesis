import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.CuspSqInt

open MeasureTheory
open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) : Frame Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) (τ : Ψ) : mat (frInv b) τ = (mat b τ)⁻¹ := rfl

theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

variable {D : D7} {Comp : Type}

end Adelic

end GlobalTheory.CuspSqInt
