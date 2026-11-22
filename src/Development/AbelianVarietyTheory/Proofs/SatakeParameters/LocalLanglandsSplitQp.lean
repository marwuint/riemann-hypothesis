import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SerChar

open GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.SplitRead

theorem det_map_units {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.toRingHom g) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [RingHom.map_det]

end GlobalTheory.SerChar
