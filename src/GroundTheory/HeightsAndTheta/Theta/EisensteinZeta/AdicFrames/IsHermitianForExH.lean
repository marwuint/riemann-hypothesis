import Mathlib
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.CompactFormulaUnitary
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Lattice
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.HeightsAndTheta.Theta.GaussianExample

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

open MeasureTheory Topology Filter Matrix TensorProduct NumberField IsDedekindDomain
  GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace
open scoped ENNReal NNReal NumberField.AdeleRing

noncomputable section

section Local

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R]
variable (ι : Type*) [Fintype ι] [DecidableEq ι] (p : ℕ)

abbrev scTop : TopologicalSpace (R ⊗[K] E) := moduleTopology R (R ⊗[K] E)

def FrameSp : Type _ := Matrix ι (Fin p) (R ⊗[K] E)

instance : AddCommGroup (FrameSp K E R ι p) :=
  inferInstanceAs (AddCommGroup (Matrix ι (Fin p) (R ⊗[K] E)))

instance : TopologicalSpace (FrameSp K E R ι p) :=
  @Pi.topologicalSpace ι _ fun _ ↦ @Pi.topologicalSpace (Fin p) _ fun _ ↦ scTop K E R

instance : MeasurableSpace (FrameSp K E R ι p) := borel _

instance : BorelSpace (FrameSp K E R ι p) := ⟨rfl⟩

def hermSub : AddSubgroup (Matrix (Fin p) (Fin p) (R ⊗[K] E)) where
  carrier := {S | (S.map (conjBase K E R))ᵀ = S}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, ha, hb]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, ha]

def HermSp : Type _ := ↥(hermSub K E R p)

instance : AddCommGroup (HermSp K E R p) := inferInstanceAs (AddCommGroup ↥(hermSub K E R p))

instance : TopologicalSpace (HermSp K E R p) :=
  TopologicalSpace.induced (fun S : ↥(hermSub K E R p) ↦ (S : Matrix (Fin p) (Fin p) (R ⊗[K] E)))
    (@Pi.topologicalSpace (Fin p) _ fun _ ↦ @Pi.topologicalSpace (Fin p) _ fun _ ↦ scTop K E R)

instance : MeasurableSpace (HermSp K E R p) := borel _

instance : BorelSpace (HermSp K E R p) := ⟨rfl⟩

variable {K E R ι p}

def HermSp.mat (S : HermSp K E R p) : Matrix (Fin p) (Fin p) (R ⊗[K] E) :=
  (show ↥(hermSub K E R p) from S).1

variable (K E R) in

def framePair (H : Matrix ι ι E) {q : ℕ} (X : Matrix ι (Fin p) (R ⊗[K] E))
    (X' : Matrix ι (Fin q) (R ⊗[K] E)) : Matrix (Fin p) (Fin q) (R ⊗[K] E) :=
  (X.map (conjBase K E R))ᵀ *
    H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E) * X'

variable (K E R) in

def gram (H : Matrix ι ι E) (X : Matrix ι (Fin p) (R ⊗[K] E)) :
    Matrix (Fin p) (Fin p) (R ⊗[K] E) :=
  framePair K E R H X X

end Local

section Adelic

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

variable (K) in

abbrev ratPts (H : Matrix ι ι E) : Subgroup (unitaryPoints K E H 𝔸[K]) :=
  (unitaryDiagonal K H).range

instance (H : Matrix ι ι E) : DiscreteTopology (ratPts K H) :=
  discreteTopology_unitaryDiagonal_range (K := K) H

end Adelic

end

end IsoFrames

end GroundTheory.Heights₂.Theta
