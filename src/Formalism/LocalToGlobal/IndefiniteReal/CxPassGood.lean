import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GoodPlacesAlt

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem sum_chars_eq {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K))
    (hinj : ∀ s t, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = Formalism.IndefR.TransferLatticeStatement.charOf (τ t) → s = t) (hX : CharsX τ Xc)
    {M : Type} [AddCommMonoid M] (F : (G → K) → M) :
    ∑ t, F (Formalism.IndefR.TransferLatticeStatement.charOf (τ t)) = ∑ χ ∈ Xc, F χ := by
  classical
  have himg : Finset.univ.image (fun t => Formalism.IndefR.TransferLatticeStatement.charOf (τ t)) = Xc := by
    ext χ
    rw [hX χ]
    simp
  rw [← himg, Finset.sum_image (fun s _ t _ h => hinj s t h)]

theorem mulVec_sum_smul {n : ℕ} (c : G → K) (M : G → Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (∑ g, c g • M g) *ᵥ x = ∑ g, c g • (M g *ᵥ x) := by
  classical
  have key : ∀ s : Finset G, (∑ g ∈ s, c g • M g) *ᵥ x = ∑ g ∈ s, c g • (M g *ᵥ x) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ← ih]
      first
        | rw [Matrix.smul_mulVec]
        | rw [Matrix.smul_mulVec_assoc]
        | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  exact key Finset.univ

theorem cpt_sum_smul (σ : K →+* ℂ) {n : ℕ} (c : G → K) (y : G → Fin n → K) :
    cpt σ (∑ g, c g • y g) = ∑ g, σ (c g) • cpt σ (y g) := by
  funext i
  simp [cpt, Finset.sum_apply, map_sum]

theorem sum_eq_one_of {E : Type} [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (ρ : G → Matrix (Fin n) (Fin n) K)
    (act : G → E →ₗ[ℂ] E) (hρ : ∀ g x, f (cpt σ (ρ g *ᵥ x)) = act g (f (cpt σ x)))
    (c : G → K) (hfix : ∀ x, ∑ g, σ (c g) • act g (f (cpt σ x)) = f (cpt σ x)) :
    ∑ g, c g • ρ g = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
  have h1 : f (cpt σ ((∑ g, c g • ρ g) *ᵥ x)) = f (cpt σ x) := by
    rw [mulVec_sum_smul, cpt_sum_smul, map_sum]
    simp only [map_smul, hρ]
    exact hfix x
  have h2 := hf h1
  funext i
  exact σ.injective (congrFun h2 i)

end GoodPlacesAlt

namespace In

end In

end Formalism.IndefR.CxPass
