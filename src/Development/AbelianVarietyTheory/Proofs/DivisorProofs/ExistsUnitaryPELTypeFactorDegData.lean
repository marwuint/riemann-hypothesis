import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHost
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodLatticeBarBar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorDegenerationDataOfUnimodularPosDef
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataUnitaryTypeStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pelOK_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ D : DegData R (maximalIdeal R), Nontrivial D.toPre.X → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dm : Datum H) (D' : DegData R (maximalIdeal R)) (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o ∧ (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D hX
  obtain ⟨E, _, _, _, ⟨H⟩⟩ := GlobalTheory.Mum.exists_host
  obtain ⟨r, W, ρ, hr, hpos, hdet, hadj, hW⟩ := GlobalTheory.Mum.unimodLattice E H
  obtain ⟨D', ⟨T⟩⟩ := _root_.GlobalTheory.Mum.TensExist.exists_tens R hR.1 D W hpos hdet
  obtain ⟨_, o, hact, hψ⟩ := GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data R hR.1 E H D D' W hpos hdet T ρ hadj hW
  obtain ⟨Dm, hDm⟩ := GlobalTheory.T.tensorDegData_unitary_type R hR E H D D' W hpos hdet T ρ hadj hW hX hr o hact hψ
  exact ⟨E, _, _, _, H, Dm, D', _, o, hDm, _root_.GlobalTheory.Mum.Tens.nonempty_factor R hR.1 D D' W hpos hdet T hr⟩

end GlobalTheory.Mum
