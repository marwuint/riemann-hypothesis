import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.RealPlaceAnalysis.StatementU

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Jet

def IsDer {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  GlRel E ∧ IsUnitary ε E ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ((∑ a, ∑ b, X a b • E a b v : V) : H) 0) ∧
    ∀ (v : V) (y : H), SmoothOnG ε (fun g => ⟪y, σ g (v : H)⟫_ℂ)

def at1 {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Arr V n 1) (a b : Fin n) : V :=
  arrOf V n 1 G (fun _ => (a, b))

namespace StdDer

def act {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :=
  (stdRep y).toLinearMap.restrict (fun _ _ => Submodule.mem_top)

theorem act_coe {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (v : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))) :
    (act y v : EuclideanSpace ℂ (Fin n)) = stdRep y v := rfl

end StdDer

end GlobalTheory.Jet
