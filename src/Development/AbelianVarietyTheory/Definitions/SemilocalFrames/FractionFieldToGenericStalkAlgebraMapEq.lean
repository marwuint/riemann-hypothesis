import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegOneNormFromCmFieldFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer

noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc
open scoped Classical

namespace GlobalTheory.SgGlob

structure ModFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (g₁ g₂ : ℕ) where
  rank : Module.finrank F E = 2
  g₁_prime : g₁.Prime
  g₂_prime : g₂.Prime
  g_ne : g₁ ≠ g₂
  A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p
  M : ∀ p, Model (A p).Fp (A p).Ep
  ok : ∀ p, (M p).OK
  de : ∀ p, (A p).Fp
  de_ne : ∀ p, de p ≠ 0
  de_gen : ∀ p (x : (A p).Fp), (haveI := (A p).ellPrime;
    ∀ y ∈ 𝒪[(A p).Fp], ‖Algebra.trace ℚ_[resChar p] (A p).Fp (x * y)‖ ≤ 1) ↔ de p * x ∈ 𝒪[(A p).Fp]
  cj_eq : ∀ p, (M p).L.cj = (A p).cj
  fractionFieldToGenericStalk_algebraMap_eq : ∀ p y, (M p).L.psi0 y = (A p).psiE (-(algebraMap (A p).Fp (A p).Ep (de p)⁻¹ * y))
  typed : ∀ p, (M p).split.isSome ↔ (resChar p = g₁ ∨ resChar p = g₂)
  split_eq : ∀ p (G : SplitG (M p).L), (M p).split = some G →
    (G.q : (A p).Fp) = (resChar p : (A p).Fp) ∧ ∃ S, (A p).split = some S ∧ S.e = G.e

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)

def uP (p : HeightOneSpectrum (𝓞 F)) : ℚ :=
  (if resChar p = g₁ ∨ resChar p = g₂ then (resChar p : ℚ) else 1) / ((g₁ : ℚ) * g₂)

def cP (p : HeightOneSpectrum (𝓞 F)) : (X.A p).Fp := X.de p * ((uP (F := F) (g₁ := g₁) (g₂ := g₂) p : ℚ) : (X.A p).Fp)

def tmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : E) : (X.A p).Ep :=
  match (X.M p).split with
  | none => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ (-ν)) * (X.A p).ιE t
  | some G => G.e.symm (X.cP p ^ (-ν) * (G.e ((X.A p).ιE t)).1 / (G.q : (X.A p).Fp),
      (-1) ^ s * X.cP p ^ (-ν) * (G.e ((X.A p).ιE t)).2 / (G.q : (X.A p).Fp))

include X in

theorem exists_unitAt_eq_inv (p : HeightOneSpectrum (𝓞 F)) :
    ∃ m : ℕ, ¬ resChar p ∣ m ∧ uP (F := F) (g₁ := g₁) (g₂ := g₂) p = (m : ℚ)⁻¹ ∧
      g₁ * g₂ = (if resChar p = g₁ ∨ resChar p = g₂ then resChar p else 1) * m := by
  have h1 : (g₁ : ℚ) ≠ 0 := by exact_mod_cast X.g₁_prime.ne_zero
  have h2 : (g₂ : ℚ) ≠ 0 := by exact_mod_cast X.g₂_prime.ne_zero
  have hp : (resChar p).Prime := (X.A p).ellPrime.out
  unfold uP
  by_cases e1 : resChar p = g₁
  · refine ⟨g₂, fun h => X.g_ne (e1 ▸ (Nat.prime_dvd_prime_iff_eq hp X.g₂_prime).1 h), ?_, by simp [e1]⟩
    rw [if_pos (Or.inl e1), e1]; field_simp
  by_cases e2 : resChar p = g₂
  · refine ⟨g₁, fun h => e1 ((Nat.prime_dvd_prime_iff_eq hp X.g₁_prime).1 h), ?_, by simp [e2, mul_comm]⟩
    rw [if_pos (Or.inr e2), e2]; field_simp
  refine ⟨g₁ * g₂, fun h => ?_, by simp [e1, e2], by simp [e1, e2]⟩
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact e1 ((Nat.prime_dvd_prime_iff_eq hp X.g₁_prime).1 h)
  · exact e2 ((Nat.prime_dvd_prime_iff_eq hp X.g₂_prime).1 h)

theorem cP_ne_zero (p : HeightOneSpectrum (𝓞 F)) : X.cP p ≠ 0 := by
  haveI := (X.A p).char0
  obtain ⟨m, hm, e, -⟩ := X.exists_unitAt_eq_inv p
  have : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  unfold cP
  rw [e]
  exact mul_ne_zero (X.de_ne p) (by simpa using this)

def xmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (x : E) : (X.A p).Ep :=
  match (X.M p).split with
  | none => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ ν) * (X.A p).ιE x
  | some G => G.e.symm (X.cP p ^ ν * (G.e ((X.A p).ιE x)).1 * (G.q : (X.A p).Fp),
      (-1) ^ s * X.cP p ^ ν * (G.e ((X.A p).ιE x)).2 * (G.q : (X.A p).Fp))

def tfac (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : (X.A p).Ep := X.tmod ν s p 1

theorem tmod_eq (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : E) :
    X.tmod ν s p t = X.tfac ν s p * (X.A p).ιE t := by
  unfold tfac tmod
  cases (X.M p).split with
  | none => simp
  | some G => apply G.e.injective; ext <;> simp <;> ring

theorem xmod_eq (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (x : E) :
    X.xmod ν s p x = X.xmod ν s p 1 * (X.A p).ιE x := by
  unfold xmod
  cases (X.M p).split with
  | none => simp
  | some G => apply G.e.injective; ext <;> simp <;> ring

theorem tfac_mul (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : X.tfac ν s p * X.xmod ν s p 1 = 1 := by
  have hc : X.cP p ^ ν ≠ 0 := zpow_ne_zero _ (X.cP_ne_zero p)
  unfold tfac tmod xmod
  cases (X.M p).split with
  | none => simp only [map_one, mul_one]; rw [← map_mul, zpow_neg, inv_mul_cancel₀ hc, map_one]
  | some G =>
    have hq : (G.q : (X.A p).Fp) ≠ 0 := fun e => G.q_irr.ne_zero (Subtype.ext e)
    have hs : ((-1 : (X.A p).Fp) ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    apply G.e.injective
    ext
    · simp only [map_one, map_mul, AlgEquiv.apply_symm_apply, Prod.fst_mul, Prod.fst_one, zpow_neg]
      field_simp
    · simp only [map_one, map_mul, AlgEquiv.apply_symm_apply, Prod.snd_mul, Prod.snd_one, zpow_neg]
      field_simp
      exact hs

theorem tmod_mul_xmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) {t : E} (ht : t ≠ 0) :
    X.tmod ν s p t * X.xmod ν s p t⁻¹ = 1 := by
  rw [tmod_eq, xmod_eq, mul_mul_mul_comm, tfac_mul, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]

theorem isUnit_tmod (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) : IsUnit (X.tmod ν s p t) :=
  IsUnit.of_mul_eq_one _ (X.tmod_mul_xmod ν s p t.ne_zero)

theorem tmod_sub (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t t' : E) :
    X.tmod ν s p (t - t') = X.tmod ν s p t - X.tmod ν s p t' := by
  simp only [tmod_eq, map_sub, mul_sub]

@[simp] theorem tmod_zero (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) : X.tmod ν s p 0 = 0 := by
  simp [tmod_eq]

def tmodU (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) : (X.A p).Epˣ :=
  if h : IsUnit (X.tmod ν s p t) then h.unit else 1

@[simp] theorem coe_tmodU (ν : ℤ) (s : ℕ) (p : HeightOneSpectrum (𝓞 F)) (t : Eˣ) :
    ((X.tmodU ν s p t : (X.A p).Epˣ) : (X.A p).Ep) = X.tmod ν s p t := by
  unfold tmodU
  rw [dif_pos (X.isUnit_tmod ν s p t), IsUnit.unit_spec]

def La (ν : ℤ) (s : ℕ) : Set E := {t | ∀ p, X.tmod ν s p t ∈ (X.M p).R}

def LaSub (ν : ℤ) (s : ℕ) : AddSubgroup E :=
  AddSubgroup.ofSub (X.La ν s) ⟨0, fun p => by simp⟩ fun t ht t' ht' p => by
    rw [← sub_eq_add_neg, tmod_sub]; exact sub_mem (ht p) (ht' p)

@[simp] theorem coe_LaSub (ν : ℤ) (s : ℕ) : (X.LaSub ν s : Set E) = X.La ν s := rfl

def Nt (ν : ℤ) (s : ℕ) (t : E) : ℝ := if t = 0 then 0 else ∏ᶠ p, ((X.M p).modK (X.tmod ν s p t))⁻¹

@[simp] theorem Nt_zero (ν : ℤ) (s : ℕ) : X.Nt ν s 0 = 0 := if_pos rfl

end ModFam

def psiInf {E : Type} [Field E] [NumberField E] (x : E) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ))

end GlobalTheory.SgGlob
