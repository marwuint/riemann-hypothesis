import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLatComap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndepSpan

noncomputable section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Sat
variable {k : Type} [Field k]

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
  {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem comap_sh (f : W →ₗ[k⸨X⸩] V) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).comap (f.restrictScalars k⟦X⟧) = sh a (N.comap (f.restrictScalars k⟦X⟧)) := by
  ext x
  simp [mem_sh_iff_smul_mem]

theorem isLat_comap (f : W →ₗ[k⸨X⸩] V) (hf : Function.Injective f) {N : Submodule k⟦X⟧ V} (hN : IsLat N) :
    IsLat (N.comap (f.restrictScalars k⟦X⟧)) :=
  _root_.GlobalTheory.LatticeComap.main f hf hN

variable [Module k V] [Module k W] {l n : ℕ} {R : RingPG k l}

theorem comap_pull (D : ModPG R n V) (D' : ModPG R n W) (i : ZMod n) (f g : W →ₗ[k⸨X⸩] V)
    (hf : Function.Injective f) (hg : Function.Injective g) (hφ : ∀ x, g (D'.φ i x) = D.φ i (f x))
    {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    (pull (D.φ i) N).comap (g.restrictScalars k⟦X⟧) = pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧)) :=
  _root_.GlobalTheory.IndependentSpanDual.comap_pull D D' i f g hf hg hφ hN

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → W →ₗ[k⸨X⸩] V), (∀ i, Function.Injective (f i)) → (∀ i x, f i (D'.φ i x) = D.φ i (f (i - 1) x)) → (∀ i x, f i (D'.γ i x) = D.γ i (f i x)) → ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) → let N' := fun i => (N i).comap ((f i).restrictScalars k⟦X⟧); (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => isLat_comap _ (hf i) (hN i), fun i => ?_, fun i x hx => ?_⟩
  · have h := comap_pull D D' i (f (i - 1)) (f i) (hf _) (hf _) (hφ i) (hN (i - 1)).1
    simp only [N']
    rw [← h, ← comap_sh, ← comap_sh]
    exact ⟨Submodule.comap_mono (hAB i).1, Submodule.comap_mono (hAB i).2⟩
  · simp only [N']
    rw [← comap_sh]
    change f i _ ∈ sh 1 (N i)
    rw [map_sub, hγ]
    exact hC i _ hx

end GlobalTheory.PhiGam.Sat
