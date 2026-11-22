import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PrincipalHartogs

theorem mem_span_singleton_of_forall_height_le_one {B : Type} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [IsNoetherianRing B] (f s : B)
    (h : ∀ q : Ideal B, q.IsPrime → q.height ≤ 1 → ∃ u, u ∉ q ∧ u * s ∈ Ideal.span {f}) :
    s ∈ Ideal.span {f} := by
  by_cases hf : f = 0
  · subst hf
    obtain ⟨u, hu, hus⟩ := h ⊥ Ideal.isPrime_bot (by simp)
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hus ⊢
    rcases mul_eq_zero.mp hus with h0 | h0
    · exact absurd (h0 ▸ Submodule.zero_mem ⊥) hu
    · exact h0
  let K := FractionRing B
  have hfK : algebraMap B K f ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hf
  let d : Ideal B := (Ideal.span {f}).colon {s}
  have hd : ∀ a, a ∈ d ↔ a * s ∈ Ideal.span {f} := fun a => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul]
  by_cases hd1 : d = ⊤
  · simpa using (hd 1).1 (hd1 ▸ Submodule.mem_top)
  exfalso
  obtain ⟨Q, hQ, hdQ⟩ := Ideal.exists_le_maximal d hd1
  have hreg : ∀ a c : B, algebraMap B K a * (algebraMap B K s / algebraMap B K f) = algebraMap B K c →
      a ∈ d := fun a c e => by
    rw [hd, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul] at e
    rw [mul_comm f c]
    exact IsFractionRing.injective B K e
  obtain ⟨p, hp, -, h1, hpf⟩ := NormalPole.exists_height_one (K := K)
    (algebraMap B K s / algebraMap B K f) Q (fun a c e => hdQ (hreg a c e))
  obtain ⟨u, hu, hus⟩ := h p hp h1.le
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hus
  refine hu (hpf u c ?_)
  rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul, hc]

end GlobalTheory.PrincipalHartogs

namespace GlobalTheory.PrincipalHartogs

end GlobalTheory.PrincipalHartogs
