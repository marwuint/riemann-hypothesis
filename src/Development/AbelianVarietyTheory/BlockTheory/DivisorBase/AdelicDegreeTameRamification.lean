import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev quadField (H : Host E) : IntermediateField ℚ E := IntermediateField.adjoin ℚ {((H.rt : 𝓞 E) : E)}

instance (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

def TameAtRamified (H : Host E) : Prop :=
  ∀ (l : ℕ) (w : Ideal (𝓞 E)), l.Prime → (l : ℤ) ∣ discr E → w.IsMaximal → (l : 𝓞 E) ∈ w →
    w.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w ∧
    (l ≠ H.d → ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ w ∧ H.bar a ∉ w) ∧
    (l = H.d → (l : 𝓞 E) ∉ w ^ 3)

section Lie

variable {H : Host E} {k : Type} [Field k] [NumberField k]

def IsEigenVec (t : SAB H (Sp k)) (χ : 𝓞 E → k) (w : epsR k ⟶ t.G) : Prop :=
  IsTangent w ∧ ∀ a, (w ≫ t.act.act a).left = spMap (epsScaleR (χ a)) ≫ w.left

def IsEigenBasis (t : SAB H (Sp k)) (χ : 𝓞 E → k) {n : ℕ} (x : Fin n → (epsR k ⟶ t.G)) : Prop :=
  (∀ i, IsEigenVec t χ (x i)) ∧ ∀ w, IsEigenVec t χ w → ∃! c : Fin n → k, IsLieComb c x w

end Lie

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
