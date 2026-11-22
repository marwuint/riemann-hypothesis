import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.ModulesPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

section Coherence

variable {X : Scheme.{u}} (F : X.Modules)

noncomputable def compHom {Y Z : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X) (c : Y ⟶ X) (h : a ≫ b = c) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj F) ⟶
      (Scheme.Modules.pullback c).obj F :=
  (Scheme.Modules.pullbackComp a b).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F

end Coherence

section Presheaf

variable {X : Scheme.{u}} (F : X.Modules)

end Presheaf

end GroundTheory.Arith.Etale
