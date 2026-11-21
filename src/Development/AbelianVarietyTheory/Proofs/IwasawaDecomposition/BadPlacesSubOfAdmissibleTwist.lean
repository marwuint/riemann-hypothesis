import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.BadV

theorem unr_of_twist {R : Ranks} {H : Host R} {S : Set ℕ} {ξ : HChar H.E} (hξ : Chr.IsTwist H S ξ) {p : ℕ} (hp : p.Prime)
    (hS : p ∈ S) (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ξ.UnrAt u := by
  by_contra hn
  obtain ⟨-, h1, -, h2⟩ := hξ.2.2.2 u hn
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) ∈ u.asIdeal := Ideal.absNorm_mem _
  by_cases e : Ideal.absNorm u.asIdeal = p
  · exact h2 (e ▸ hS)
  · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) (p : 𝓞 H.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
    exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hu)))

theorem not_unr_of_delta {R : Ranks} {H : Host R} {p : ℕ} {δ : HChar H.E} (hδ : IsDelta (H := H) p δ)
    (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ¬ δ.UnrAt u := by
  intro hn
  have h15 := (hδ.ine u hu 1).1 fun y hy => by rw [pow_one]; exact hn y hy
  exact absurd h15 (by decide)

theorem unr_of_mul_left {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : (χ * χ').UnrAt u) : χ'.UnrAt u := fun y hy => by
  have e := h' y hy
  rwa [HChar.loc_mul, h y hy, one_mul] at e

theorem unr_of_mul_right {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ'.UnrAt u) (h' : (χ * χ').UnrAt u) : χ.UnrAt u := fun y hy => by
  have e := h' y hy
  rwa [HChar.loc_mul, h y hy, mul_one] at e

end GlobalTheory.LevCmp.BadV
