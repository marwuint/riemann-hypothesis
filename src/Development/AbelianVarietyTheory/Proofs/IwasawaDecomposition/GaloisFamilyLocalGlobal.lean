import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SysFin

open GlobalTheory.CoefDuty

section Places
variable {R : Ranks} {H : Host R}

theorem intCast_mem_conj {v w : PlE H} (h : IsConjPl H v w) (n : ℤ) :
    (n : 𝓞 H.E) ∈ v.asIdeal ↔ (n : 𝓞 H.E) ∈ w.asIdeal :=
  h _ _ (by simp [map_intCast])

theorem intCast_mem_over {w : PlE H} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield H.E))}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield H.E)) (𝓞 H.E)) = v.asIdeal) (n : ℤ) :
    (n : 𝓞 H.E) ∈ w.asIdeal ↔ (n : 𝓞 (maximalRealSubfield H.E)) ∈ v.asIdeal := by
  rw [← h, Ideal.mem_comap, map_intCast]

end Places

theorem finite_intCast_mem {K : Type} [Field K] [NumberField K] (N : ℤ) (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (N : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(N : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem exists_intCast_mem {K : Type} [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : 𝓞 K) ∈ q.asIdeal := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot q.ne_bot
  have h := Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨n, hn0, ?_⟩
  rw [Ideal.mem_comap, eq_intCast] at hn
  exact hn

theorem intCast_mem_of_dvd {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {n N : ℤ} (hd : n ∣ N)
    (h : (n : 𝓞 K) ∈ v.asIdeal) : (N : 𝓞 K) ∈ v.asIdeal := by
  obtain ⟨b, rfl⟩ := hd
  push_cast
  exact Ideal.mul_mem_right _ _ h

section Eig
variable {D : D7}

theorem genAt_mono {l : ℕ} {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q') {v : PlE D.host} {k : ℕ}
    (h : GenAt D l Q' v k) : GenAt D l Q v k :=
  ⟨h.1, h.2.1, h.2.2.1, fun hv => h.2.2.2.1 (hQ hv), h.2.2.2.2⟩

open Classical in
theorem eigSet_restrict {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) (l : ℕ) {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q')
    {c : PlE D.host → ℕ → ℂ} (hc : c ∈ EigSet X l Q) :
    (fun v k => if GenAt D l Q' v k then c v k else 0) ∈ EigSet X l Q' := by
  obtain ⟨-, y, hy, hy'⟩ := hc
  refine ⟨fun v k hg => if_neg hg, y, hy, fun v k s ϖ hg hcj hu => ?_⟩
  simp only [if_pos hg]
  exact hy' v k s ϖ (genAt_mono hQ hg) hcj hu

theorem eigSet_transport (M : MtFam D) {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) (l : ℕ) (Q : Finset (PlE D.host))
    (c : PlE D.host → ℕ → ℂ) : c ∈ EigSet (M μ j a1 a2) l Q → c ∈ EigSet (M μ' j' b1 b2) l Q := by
  subst hμ hj; exact id

end Eig

end GlobalTheory.SysFin

end
