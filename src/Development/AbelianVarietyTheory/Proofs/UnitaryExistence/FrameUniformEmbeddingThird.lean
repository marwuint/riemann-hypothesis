import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEquivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem coset_fv_mulVec (A : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (A.map (inclR (F := F) (Af F))) *ᵥ AdLat.fv F x = AdLat.fv F (A *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (Af F)) A x i).symm

theorem coset_tmul_eq (t : Af F) (x : Fin n → E) :
    (fun i => t ⊗ₜ[F] x i : Fin n → AdLat.RA F E) = (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • AdLat.fv F x := by
  funext i
  simp only [AdLat.fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem coset_smul_mem_hat (L : Set (Fin n → E)) (t : Af F) (ht : ∀ v, t v ∈ v.adicCompletionIntegers F)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (t ⊗ₜ[F] (1 : E) : AdLat.RA F E) • w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨t * s, fun v => mul_mem (ht v) (hs v), x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem coset_mulVec_mem_hat (L : Set (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) (hA : ∀ x ∈ L, A *ᵥ x ∈ L)
    (w : Fin n → AdLat.RA F E) (hw : w ∈ AdLat.hat F L) :
    (A.map (inclR (F := F) (Af F))) *ᵥ w ∈ AdLat.hat F L := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, x, hx, rfl⟩ := hw
    rw [coset_tmul_eq, Matrix.mulVec_smul, coset_fv_mulVec]
    exact coset_smul_mem_hat L s hs _ (AdLat.Half.fv_mem_hat' L _ (hA x hx))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [Matrix.mulVec_add]; exact add_mem h h'
  | neg w _ h => rw [Matrix.mulVec_neg]; exact neg_mem h

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coset_latGHat (V : HSp D) (g : GA D V) :
    latGHat V g = AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨hfg, hsp, h⟩ := comp_latG D V
  obtain ⟨Λ, h1, -, -, h2⟩ := AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (latG V 1) (finHom V g) hfg hsp
  apply SetLike.coe_injective
  rw [(h g).2, (h g).1, ← h1, h2]

theorem coset_fin {R : Type} [CommRing R] {n : ℕ} (S T : AddSubgroup (Fin n → R)) (g₁ g₂ δ : GL (Fin n) R) (N : ℕ)
    (h1 : ∀ w ∈ T, ∃ z ∈ S, g₁.1 *ᵥ z = w) (hδ : ∀ w ∈ T, δ.1 *ᵥ w ∈ T) (hδ' : ∀ w ∈ T, (δ⁻¹).1 *ᵥ w ∈ T)
    (u v w₁ w₂ b : Fin n → R) (hw₁ : w₁ ∈ T) (hw₂ : w₂ ∈ T) (hb : b ∈ T)
    (e₁ : u - g₁.1 *ᵥ v = N • w₁) (e₂ : u - g₂.1 *ᵥ v = N • w₂) (e₃ : δ.1 *ᵥ u = u + N • b) :
    ∃ y ∈ S, ((δ * g₁)⁻¹ * g₂).1 *ᵥ v - v = N • y := by
  obtain ⟨z, hz, ez⟩ := h1 _ (hδ' _ (sub_mem (sub_mem (hδ _ hw₁) hw₂) hb))
  refine ⟨z, hz, ?_⟩
  have hz' : (δ * g₁).1 *ᵥ z = δ.1 *ᵥ w₁ - w₂ - b := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ez, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv : ∀ x, ((δ * g₁)⁻¹).1 *ᵥ ((δ * g₁).1 *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have e : g₂.1 *ᵥ v - (δ * g₁).1 *ᵥ v = N • ((δ * g₁).1 *ᵥ z) := by
    rw [hz', Units.val_mul, ← Matrix.mulVec_mulVec, smul_sub, smul_sub, ← Matrix.mulVec_smul, ← e₁, ← e₂,
      Matrix.mulVec_sub, e₃]
    abel
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  have e' := congrArg (fun x => ((δ * g₁)⁻¹).1 *ᵥ x) e
  simpa only [Matrix.mulVec_sub, Matrix.mulVec_smul, hinv] using e'

end GlobalTheory.RecDict
