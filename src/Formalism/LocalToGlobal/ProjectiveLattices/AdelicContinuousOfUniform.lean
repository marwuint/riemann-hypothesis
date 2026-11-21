import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

theorem bcSp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : Gx (spMap ψ ≫ x) ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom ≫ spMap ψ)
    (pullback.snd (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom)
    (by rw [Category.assoc]; exact pullback.condition)

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [Over.snd_left, Over.snd_left]
  exact pullback.lift_snd _ _ _

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Over.fst_left, Over.fst_left]
  exact pullback.lift_fst _ _ _

theorem bcOver {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (h : x ≫ Xo.s = sOf c S) : (spMap ψ.toRingHom ≫ x) ≫ Xo.s = sOf c T := by
  rw [Category.assoc, h]
  unfold sOf
  rw [bcSp]
  congr 1
  ext a
  simp

end BC

end Formalism.L2.Pj
