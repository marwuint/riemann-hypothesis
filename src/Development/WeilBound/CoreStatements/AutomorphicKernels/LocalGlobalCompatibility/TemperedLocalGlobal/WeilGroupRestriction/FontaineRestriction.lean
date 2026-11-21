import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.WdRestrict
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.Pst

namespace PositivityTheory.Pf1.CLGD.K.FontaineRestriction

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]

theorem wdRes_eq {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') :
    PositivityTheory.Pf1.CLGD.DescRes.WD.res h h' = PositivityTheory.Pf1.CLGD.WdRestrict.WD.res h h' := rfl

end PositivityTheory.Pf1.CLGD.K.FontaineRestriction

namespace PositivityTheory.Pf1.CLGD.K

end PositivityTheory.Pf1.CLGD.K
