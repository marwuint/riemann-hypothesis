import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder

noncomputable section

def stdLattice (K : Type*) [Field K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.span (𝓞 K) (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K))

def coordProj {K : Type*} [Field K] {n m k : ℕ} (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) :
    (Fin n → K) →ₗ[K] (Fin k → K) :=
  LinearMap.funLeft K K Sum.inr ∘ₗ B.equivFun.toLinearMap

def LinesLatticeBasis.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι],
    Fintype.card ι = Module.finrank ℚ V → ∀ M : Submodule ℤ V, Submodule.IsLattice ℚ M →
      ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b)

def LinesGenIndexDet.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    [DecidableEq ι] (bA bB : Module.Basis ι ℚ V) (A B : AddSubgroup V),
    A = AddSubgroup.closure (Set.range bA) → B = AddSubgroup.closure (Set.range bB) →
      genIndex A B = |((bA.det bB : ℚ) : ℝ)|

def LinesIsLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (M : Submodule (𝓞 K) (ι → K)),
    (M.restrictScalars ℤ).FG → Submodule.span K (M : Set (ι → K)) = ⊤ →
      Submodule.IsLattice ℚ (M.restrictScalars ℤ)

def LinesGenIndexTrans.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (A B C : Submodule ℤ V),
    Submodule.IsLattice ℚ A → Submodule.IsLattice ℚ B → Submodule.IsLattice ℚ C →
      0 < genIndex A.toAddSubgroup B.toAddSubgroup ∧
        genIndex A.toAddSubgroup B.toAddSubgroup * genIndex B.toAddSubgroup C.toAddSubgroup =
          genIndex A.toAddSubgroup C.toAddSubgroup

def LinesIdealLatticeFG.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K),
    (∀ x, a x ≠ 0) →
      (idealLattice a).FG ∧ Submodule.span K (idealLattice a : Set (Fin n → K)) = ⊤

end

end GroundTheory.Heights₂.Heights
