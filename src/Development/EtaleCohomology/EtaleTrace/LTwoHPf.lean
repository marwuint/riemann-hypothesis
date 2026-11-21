import Development.EtaleCohomology.EtaleTrace.LCoprodInjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

instance : PreservesLimitsOfSize.{0, 0} (disc : PSh ⥤ Spc) := by
  unfold disc SimplicialObject.const
  infer_instance

instance : PreservesLimitsOfSize.{0, 0} (sch : Scheme.{0} ⥤ Spc) := by
  unfold sch
  infer_instance

end LateralTheory.EtaleTrace
