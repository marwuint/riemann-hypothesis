import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open GlobalTheory.FramePull GlobalTheory.ConstFam

theorem exists_pt {S : Scheme.{0}} {G : Over S} (T : Over S) {Y : Scheme.{0}} (a : Y ⟶ T.left) (b : Y ⟶ G.left)
    (h : a ≫ T.hom = b ≫ G.hom) : ∃ ρ : Y ⟶ (T ⊗ G).left, ρ ≫ (fst T G).left = a ∧ ρ ≫ (snd T G).left = b :=
  ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end Frames

end GlobalTheory.TorRef
