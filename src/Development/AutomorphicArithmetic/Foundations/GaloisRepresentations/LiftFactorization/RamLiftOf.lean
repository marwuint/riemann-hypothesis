import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.PolFalseIff

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def StrongOf : Prop := LiftUnr → RamSph → GlobalTheory.Published.ArthurClozelStrongTC

end UpperTheory.Gal.AbelianGaloisNormality
