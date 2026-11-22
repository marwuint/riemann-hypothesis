import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigIterateApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlPiEquivSymmContinuous
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TwOrbFin

section Generic

variable {H : Type} [Group H]

def Bnd (K₀ : Subgroup H) (D : Set H) : Prop := ∃ S : Finset H, ∀ d ∈ D, ∃ s ∈ S, ∃ k ∈ K₀, d = s * k

def Cmd (K₀ : Subgroup H) : Prop := ∀ s : H, ∃ S : Finset H, ∀ k ∈ K₀, ∃ s' ∈ S, ∃ k' ∈ K₀, k * s = s' * k'

variable {K₀ : Subgroup H}

theorem Bnd.mul (hc : Cmd K₀) {D E : Set H} (hD : Bnd K₀ D) (hE : Bnd K₀ E) :
    Bnd K₀ {g | ∃ d ∈ D, ∃ e ∈ E, g = d * e} := by
  choose Sc hSc using hc
  obtain ⟨S, hS⟩ := hD
  obtain ⟨T, hT⟩ := hE
  refine ⟨S.biUnion fun s => T.biUnion fun t => (Sc t).image (s * ·), ?_⟩
  rintro g ⟨d, hd, e, he, rfl⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  obtain ⟨t, ht, l, hl, rfl⟩ := hT e he
  obtain ⟨s', hs', k', hk', e'⟩ := hSc t k hk
  refine ⟨s * s', Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image.2 ⟨s', hs', rfl⟩⟩⟩,
    k' * l, K₀.mul_mem hk' hl, ?_⟩
  calc s * k * (t * l) = s * (k * t) * l := by group
    _ = _ := by rw [e']; group

theorem Bnd.map (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) {D : Set H} (hD : Bnd K₀ D) : Bnd K₀ (θ '' D) := by
  obtain ⟨S, hS⟩ := hD
  refine ⟨S.image θ, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  exact ⟨θ s, Finset.mem_image.2 ⟨s, hs, rfl⟩, θ k, hθ k hk, map_mul θ s k⟩

end Generic

end GlobalTheory.TwOrbFin
