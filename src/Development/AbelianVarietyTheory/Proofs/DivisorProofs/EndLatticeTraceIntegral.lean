import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral

noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix Polynomial GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem isIntegral_of_mapsTo_lattice (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (Y : Matrix (Fin r) (Fin r) E)
    (hY : ∀ x ∈ Λ, Y *ᵥ x ∈ Λ) : IsIntegral (𝓞 E) Y := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  let f : Module.End (𝓞 E) Λ :=
    { toFun := fun x => ⟨Y *ᵥ (x : Fin r → E), hY _ x.2⟩
      map_add' := fun x y => by ext1; simp [mulVec_add]
      map_smul' := fun c x => by ext1; simp [mulVec_smul] }
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (𝓞 E) f
  have key : ∀ q : (𝓞 E)[X], ∀ x (hx : x ∈ Λ), aeval Y q *ᵥ x = ((aeval f q ⟨x, hx⟩ : Λ) : Fin r → E) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x hx
      simp only [aeval_C]
      rw [show (algebraMap (𝓞 E) (Matrix (Fin r) (Fin r) E)) a = Matrix.diagonal (fun _ => (a : E)) from rfl]
      ext i
      rw [mulVec_diagonal, Module.algebraMap_end_apply]
      rfl
    | add p q hp hq =>
      intro x hx
      rw [map_add, add_mulVec, hp x hx, hq x hx, map_add]
      rfl
    | monomial n a ih =>
      intro x hx
      have e1 : aeval Y (C a * X ^ (n + 1)) = aeval Y (C a * X ^ n) * Y := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      have e2 : aeval f (C a * X ^ (n + 1)) = aeval f (C a * X ^ n) * f := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      rw [e1, e2, ← mulVec_mulVec, ih _ (hY x hx)]
      rfl
  have hker : ∀ v, aeval Y p *ᵥ v = 0 := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => rw [key p x hx, hp0]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mulVec_smul, hx, smul_zero]
  have hA : aeval Y p = 0 := by
    apply Matrix.toLin'.injective
    ext v i
    simp [Matrix.toLin'_apply, hker]
  exact ⟨p, hp, by rw [← aeval_def]; exact hA⟩

end GlobalTheory.LieDisc
