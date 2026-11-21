import Mathlib

noncomputable section

open scoped Classical

namespace PI.IsoDetDefs

open NumberField IsDedekindDomain Module

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L

def locLen (p : Ideal R) [p.IsPrime] (A B : Submodule R V) : ℕ :=
  (Module.length R ((localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype)).toNat

def lidx (p : Ideal R) [p.IsPrime] (A B : Submodule R V) : ℤ :=
  (locLen p A (A ⊓ B) : ℤ) - locLen p B (A ⊓ B)

end Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

end PI.IsoDetDefs

namespace PI

end PI
