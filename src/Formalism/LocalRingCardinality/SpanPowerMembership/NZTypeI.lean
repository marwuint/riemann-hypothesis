import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

namespace NZ

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)
  [NumberField what₂.LL] [StarRing what₂.LL] {LL0 : IntermediateField ℚ what₂.LL}
  (C : TwCore R H what₂ LL0 (ndG H Lb what₂ h))

instance : IsEmpty (ndG H Lb what₂ h).Loc := ⟨fun i => Empty.elim i⟩

end NZ

end Formalism.BasicNotions.Examples₂
