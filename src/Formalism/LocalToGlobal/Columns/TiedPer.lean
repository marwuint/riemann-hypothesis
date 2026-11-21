import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.RecordInst

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

end GSD.Ev

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure Dua (S S' : GSD K) where
  eG : S.G ≃ S'.G
  eD : S.D ≃ S'.D
  smul : ∀ (g : S.G) (d : S.D), eD (g • d) = eG g • eD d

  B : S.V →ₗ[K] S'.V →ₗ[K] K
  inv : ∀ (g : S.G) (x : S.V) (y : S'.V), B (S.ρ g x) (S'.ρ (eG g) y) = B x y
  repr : ∀ ℓ : S.V →ₗ[K] K, ∃ y : S'.V, ∀ x, B x y = ℓ x
  ext : ∀ y y' : S'.V, (∀ x, B x y = B x y') → y = y'

namespace Dua

variable {S S' : GSD K} (P : Dua S S') (σ : K →+* ℂ)

def semi (y : S'.V) : S.V →ₛₗ[σ] ℂ where
  toFun x := σ (P.B x y)
  map_add' x x' := by rw [map_add, LinearMap.add_apply, map_add]
  map_smul' a x := by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]

theorem semi_apply (y : S'.V) (x : S.V) : P.semi σ y x = σ (P.B x y) := rfl

variable {σ} (E : S.Ev σ) {ι : Type} [Fintype ι]

def jOf (b : ι → S'.EqFun) (z : ι → ℂ) : S.Cl → E.Y → ℂ :=
  fun c => ∑ a, starRingEnd ℂ (z a) • E.sharp (P.semi σ ((b a : S'.D → S'.V) (P.eD (S.outSec.rep c))))

end Dua

end GSD

section Pair

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem per_pair_smul (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (s t : K) (hst : s * t = 1) (x y : VV K lam) :
    pairBK lam (s • rhoVr emb lam γ x) (t • rhoV emb lam γ y) = pairBK lam x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [pairingBInvariant_holds, ← mul_assoc, mul_comm t s, hst, one_mul]

theorem per_pair_repr [CharZero K] (lam : ι → DomWeight n) (ℓ : VV K lam →ₗ[K] K) : ∃ y : VV K lam, ∀ x, pairBK lam x y = ℓ x := by
  have hnd := pairingBNondegenerate_holds K ι n lam
  have hinj : Function.Injective (pairBK (K := K) lam).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hnd.2 y fun x => LinearMap.congr_fun hy x
  have : FiniteDimensional K (VV K lam) := Module.Finite.of_basis (bVV K lam)
  have hsurj : Function.Surjective (pairBK (K := K) lam).flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨y, hy⟩ := hsurj ℓ
  exact ⟨y, fun x => by rw [← hy]; rfl⟩

theorem per_pair_ext [CharZero K] (lam : ι → DomWeight n) (y y' : VV K lam) (h : ∀ x, pairBK lam x y = pairBK lam x y') : y = y' := by
  have hnd := pairingBNondegenerate_holds K ι n lam
  rw [← sub_eq_zero]
  exact hnd.2 _ fun x => by rw [map_sub, h x, sub_self]

end Pair

section Xp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {SG' : Finset (HeightOneSpectrum (𝓞 X.E))}
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

theorem per_chr_mul {n : ℕ} (Λ : LevFam X.E X.K n SG') (h : ↥Λ.grp) :
    ((Λ.inv.chr (⟨h.1, h.2⟩ : ↥Λ.inv.grp) : X.Kˣ) : X.K) * ((Λ.chr h : X.Kˣ) : X.K) = 1 := by
  rw [Λ.inv_chr, ← Units.val_mul, inv_mul_cancel, Units.val_one]

def perDua : GSD.Dua (ptGSD W ΛM) (rowGSD W ΛM) where
  eG := ⟨fun g => (g.1, ⟨g.2.1, g.2.2⟩), fun g => (g.1, ⟨g.2.1, g.2.2⟩), fun _ => rfl, fun _ => rfl⟩
  eD := Equiv.refl _
  smul := fun _ _ => rfl
  B := pairBK W.sgTrue
  inv := fun g x y => per_pair_smul X.emb W.sgTrue (ufGL X.E _ g.1) _ _ (per_chr_mul ΛM ⟨g.2.1, g.2.2⟩) x y
  repr := per_pair_repr W.sgTrue
  ext := per_pair_ext W.sgTrue

variable (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (hM : (rowGSD W ΛM).Ok)

theorem per_jMCL_eq (z : Fin ((rowGSD W ΛM).hDim hM) → ℂ) :
    jMCL W ΛM σ₀ hσ hM z = (perDua W ΛM).jOf (ptEv W ΛM σ₀ hσ) ((rowGSD W ΛM).hB hM) z := rfl

end Xp

end Formalism.L2.Col
