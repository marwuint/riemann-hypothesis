import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsAlt
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RecAlgNormDiag
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IsoComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.AttResProof

theorem algSat_pow (a q f : ℕ) (B : Multiset ℂˣ) :
    algSat a (q ^ f) (B.map (· ^ f)) = (algSat a q B).map (· ^ f) := by
  unfold algSat
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, Units.val_pow_eq_pow_val, mul_pow]
  congr 1
  push_cast
  rw [← Complex.ofReal_pow, Real.rpow_pow_comm (Nat.cast_nonneg q)]

end GlobalTheory.RealGal.AttResProof
