import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBC0OfQuadBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SelfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.WeakEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SplitOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcAtt0
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ConjAlgebraMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcDual0
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

namespace UpperTheory.V.Br

theorem quadBCw_of_quadBC0 (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hC : ExC) (hR : ExR) (h : QuadBC0) : QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a _ ha π hr
  refine (h F E h2 a ha π hr).imp_right fun ⟨P, hP⟩ => ⟨P, hP, fun hreg ⟨χ, hχ⟩ => ?_⟩
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  exact splitOf hN hC hR F E h2 a ha π χ P hreg hχ hP

theorem quadBCw (P : Hypotheses₂) : QuadBCw :=
  quadBCw_of_quadBC0 P.litN (galoisExistence_from_published P) (realExistence_from_published P) P.bc

end UpperTheory.V.Br
