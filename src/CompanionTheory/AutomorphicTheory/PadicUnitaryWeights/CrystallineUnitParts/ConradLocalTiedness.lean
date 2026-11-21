import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace CompanionTheory.PRW.ACWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

def ent {G : Type} [Group G] {LL : FinExt l} (ψ : G →* GL (Fin 1) ↥LL.1) (g : G) : Qbar l :=
  (((ψ g : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 : ↥LL.1)

end CompanionTheory.PRW.ACWD

end
