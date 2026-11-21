import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.CoverChart

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := (Spec.map_comp _ _)

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem gen_eq' {G : Scheme.{0}} [IsIntegral G] (z : G) :
    spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ G.fromSpecStalk z = G.fromSpecStalk (genericPoint G) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)

theorem stalk_eq (z : V.G) :
    spMap (V.π.stalkMap z).hom ≫ Y.X.fromSpecStalk (V.π z) = V.G.fromSpecStalk z ≫ V.π :=
  Scheme.SpecMap_stalkMap_fromSpecStalk V.π

theorem alg_comp_stalkMap (z : V.G) :
    (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom =
      V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField) := by
  have h : spMap ((algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom) ≫
        Y.X.fromSpecStalk (V.π z) =
      spMap (V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField)) ≫ Y.X.fromSpecStalk (V.π z) := by
    rw [sp_comp, sp_comp, Category.assoc, Category.assoc, stalk_eq, gen_eq', ← Category.assoc, gen_eq', V.φ_spec]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

end GlobalTheory.HtGen.CoverChart

