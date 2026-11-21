import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def conjE {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) : HomE E m n ≃ₗ[𝓞 E] HomE E m n where
  toFun x := g'.toLinearMap ∘ₗ x ∘ₗ g.symm.toLinearMap
  invFun y := g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap
  map_add' x y := LinearMap.ext fun v => by simp
  map_smul' r x := LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, RingHom.id_apply]
    exact equiv_osmul g' r _
  left_inv x := LinearMap.ext fun v => by simp
  right_inv y := LinearMap.ext fun v => by simp

theorem conjE_apply {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) (x : HomE E m n) :
    conjE g g' x = g'.toLinearMap ∘ₗ x ∘ₗ g.symm.toLinearMap := rfl

theorem conjE_symm_apply {m n : ℕ} (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n) (y : HomE E m n) :
    (conjE g g').symm y = g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap := rfl

theorem homAt_gmap {m n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E m ≃ₗ[E] Sp E m) (g' : Sp E n ≃ₗ[E] Sp E n)
    (N : Submodule (𝓞 E) (Sp E m)) (N' : Submodule (𝓞 E) (Sp E n)) :
    homAt S (gmap g N) (gmap g' N') = (homAt S N N').map (conjE g g' : HomE E m n →ₗ[𝓞 E] HomE E m n) := by
  ext x
  rw [Submodule.mem_map_equiv]
  change (∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal (gmap g N), x y ∈ localization₂ P.asIdeal (gmap g' N')) ↔
    ∀ P ∈ S, ∀ u ∈ localization₂ P.asIdeal N, ((conjE g g').symm x) u ∈ localization₂ P.asIdeal N'
  constructor
  · intro h P hP u hu
    have h1 := h P hP (g u) ((mem_localization_gmap P g N (g u)).2 (by simpa using hu))
    rw [mem_localization_gmap] at h1
    simpa [conjE_symm_apply] using h1
  · intro h P hP y hy
    rw [mem_localization_gmap]
    have h1 := h P hP (g.symm y) ((mem_localization_gmap P g N y).1 hy)
    simpa [conjE_symm_apply] using h1

theorem divLat_map {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (Φ : H ≃ₗ[𝓞 E] H) (c : ℕ) (M : Submodule (𝓞 E) H) :
    divLat c (M.map (Φ : H →ₗ[𝓞 E] H)) = (divLat c M).map (Φ : H →ₗ[𝓞 E] H) := by
  ext x
  rw [Submodule.mem_map_equiv]
  simp only [divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mem_map_equiv, map_smul]

theorem mulLat_map {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (Φ : H ≃ₗ[𝓞 E] H) (c : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat c (M.map (Φ : H →ₗ[𝓞 E] H)) = (mulLat c M).map (Φ : H →ₗ[𝓞 E] H) := by
  unfold mulLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext v
  simp

theorem latSum_map {H M : Type} [AddCommGroup H] [Module (𝓞 E) H] [AddCommMonoid M] (Φ : H ≃ₗ[𝓞 E] H)
    (A B : Submodule (𝓞 E) H) (F : H → M) (hF : ∀ x z, z ∈ B.map (Φ : H →ₗ[𝓞 E] H) → F (x + z) = F x) :
    latSum (A.map (Φ : H →ₗ[𝓞 E] H)) (B.map (Φ : H →ₗ[𝓞 E] H)) F = latSum A B (fun x => F (Φ x)) := by
  unfold latSum
  let eA : ↥A ≃ₗ[𝓞 E] ↥(A.map (Φ : H →ₗ[𝓞 E] H)) := Φ.submoduleMap A
  have hq : (B.comap A.subtype).map (eA : ↥A →ₗ[𝓞 E] ↥(A.map (Φ : H →ₗ[𝓞 E] H))) = (B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype := by
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.mem_map_equiv]
    rfl
  let q := Submodule.Quotient.equiv _ _ eA hq
  rw [← finsum_comp_equiv q.toEquiv]
  apply finsum_congr
  intro w
  set s := Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) w
  set r := Function.surjInv (Submodule.Quotient.mk_surjective ((B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype)) (q.toEquiv w)
  have hs : Submodule.Quotient.mk s = w := Function.surjInv_eq _ w
  have hr : Submodule.Quotient.mk r = q.toEquiv w := Function.surjInv_eq _ _
  have hrs : Submodule.Quotient.mk r = (Submodule.Quotient.mk (eA s) : ↥(A.map (Φ : H →ₗ[𝓞 E] H)) ⧸ (B.map (Φ : H →ₗ[𝓞 E] H)).comap (A.map (Φ : H →ₗ[𝓞 E] H)).subtype) := by
    rw [hr, ← hs]; rfl
  rw [Submodule.Quotient.eq] at hrs
  have hd : ((r : H) - Φ (s : H)) ∈ B.map (Φ : H →ₗ[𝓞 E] H) := hrs
  have := hF (Φ (s : H)) _ hd
  rw [add_sub_cancel] at this
  exact this

theorem isSdLat_gmap {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (γ : UF E n) : IsSdLat (gmap γ.1 N) := by
  refine ⟨gmap_lattice γ.1 N hN.1, ?_⟩
  change dual (hStd E n) (gmap γ.1 N) = gmap γ.1 N
  rw [dual_gmap γ.1 γ.2, hN.2]

variable {K : Type} [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end Formalism.L2.Ker
