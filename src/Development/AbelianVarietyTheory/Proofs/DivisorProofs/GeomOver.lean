import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SectionOfFreeOnUnitComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

abbrev geomX (A : AbVar K) : Scheme.{0} := GlobalTheory.Et.geom (AlgebraicClosure K) A.X.hom

abbrev geomOver (A : AbVar K) : Over (Sp K) :=
  Over.mk (pullback.fst A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) ≫ A.X.hom)

def transl (A : AbVar K) (a : A.Pt) : geomX A ⟶ geomX A :=
  pullback.lift
    ((lift (Over.homMk (pullback.fst _ _) : geomOver A ⟶ A.X)
      (Over.homMk (pullback.snd _ _ ≫ a.left) (by
        rw [Category.assoc, Over.w a]; exact pullback.condition.symm) : geomOver A ⟶ A.X) ≫ μ[A.X]).left)
    (pullback.snd _ _) (by
      rw [Over.w]; exact pullback.condition)

end GlobalTheory.AV.AbVar
