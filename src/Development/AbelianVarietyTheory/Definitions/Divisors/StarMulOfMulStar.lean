import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemShaKernelIffLocallyTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsingletonComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootEquivMk

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LKInv

open GlobalTheory.LKTorus

section General

variable (k : Type) [Field k] {B L : Type} [Ring B] [StarRing B] [Algebra k B] [CommRing L] [Algebra k L]

variable {k}

theorem inv_comm {γ₀ : B} (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) :
    ((u⁻¹ : Bˣ) : B) * γ₀ = γ₀ * ((u⁻¹ : Bˣ) : B) :=
  calc ((u⁻¹ : Bˣ) : B) * γ₀ = ((u⁻¹ : Bˣ) : B) * (γ₀ * u) * ((u⁻¹ : Bˣ) : B) := by
        rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    _ = ((u⁻¹ : Bˣ) : B) * ((u : B) * γ₀) * ((u⁻¹ : Bˣ) : B) := by rw [hu]
    _ = γ₀ * ((u⁻¹ : Bˣ) : B) := by rw [← mul_assoc, Units.inv_mul, one_mul]

def liftUnit (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) : Lˣ where
  val := ((hcent u).1 hu).choose
  inv := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose
  val_inv := hι (by
    have h1 := ((hcent u).1 hu).choose_spec
    have h2 := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose_spec
    rw [map_mul, h1, h2, Units.mul_inv, map_one])
  inv_val := hι (by
    have h1 := ((hcent u).1 hu).choose_spec
    have h2 := ((hcent ((u⁻¹ : Bˣ) : B)).1 (inv_comm u hu)).choose_spec
    rw [map_mul, h1, h2, Units.inv_mul, map_one])

@[simp] theorem ι_liftUnit (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (u : Bˣ) (hu : (u : B) * γ₀ = γ₀ * u) :
    ι ((liftUnit ι hι γ₀ hcent u hu : Lˣ) : L) = u :=
  ((hcent u).1 hu).choose_spec

def cocyc (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[k] L)
    (hc : ∀ a, ι (c a) = star (ι a)) (g : Bˣ) (hg : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B)) :
    fixU k c :=
  ⟨liftUnit ι hι γ₀ hcent (star g * g) hg, hι (by
    rw [hc, ι_liftUnit, Units.val_mul, Units.coe_star, star_mul, star_star])⟩

@[simp] theorem ι_cocyc (ι : L →ₐ[k] B) (hι : Function.Injective ι) (γ₀ : B)
    (hcent : ∀ x : B, x * γ₀ = γ₀ * x ↔ x ∈ Set.range ι) (c : L →ₐ[k] L)
    (hc : ∀ a, ι (c a) = star (ι a)) (g : Bˣ) (hg : ((star g * g : Bˣ) : B) * γ₀ = γ₀ * ((star g * g : Bˣ) : B)) :
    ι (((cocyc ι hι γ₀ hcent c hc g hg : fixU k c) : Lˣ) : L) = star (g : B) * g := by
  simp [cocyc]

end General

section Local

variable (S : Type) [Field S] [CharZero S] {B L : Type} [Ring B] [StarRing B] [Algebra ℚ B] [CommRing L]
  [Algebra ℚ L]

def locElt (γ₀ : Bˣ) : (S ⊗[ℚ] B)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] S ⊗[ℚ] B).toMonoidHom γ₀

@[simp] theorem coe_locElt (γ₀ : Bˣ) : ((locElt S γ₀ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) = (1 : S) ⊗ₜ[ℚ] (γ₀ : B) :=
  rfl

variable {S}

end Local

end GlobalTheory.LKInv

