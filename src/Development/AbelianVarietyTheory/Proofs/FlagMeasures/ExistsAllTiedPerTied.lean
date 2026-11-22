import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NEqAndIsClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrability
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.Per.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Iterated

variable {G N : Type} [MeasurableSpace G] [MeasurableSpace N] {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N}
  {P P' R : G → N → ℂ}

theorem iterated_add (h : (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ)
    (h' : (∀ g, IntegrableOn (P' g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P' g n ∂ν) 𝓕 μ)
    (hR : ∀ g n, R g n = P g n + P' g n) :
    ∫ g in 𝓕, ∫ n in 𝓝, R g n ∂ν ∂μ = ∫ g in 𝓕, ∫ n in 𝓝, P g n ∂ν ∂μ + ∫ g in 𝓕, ∫ n in 𝓝, P' g n ∂ν ∂μ := by
  rw [← integral_add h.2 h'.2]
  congr 1
  funext g
  rw [← integral_add (h.1 g) (h'.1 g)]
  simp only [hR]

end Iterated

variable {D : D7}

theorem flag_topology (B : HSp D) {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) :
    LocallyCompactSpace (NFlag B e) ∧ SecondCountableTopology (NFlag B e) ∧ BorelSpace (NFlag B e) ∧
      Countable (NFlagQ B e) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  haveI : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
    DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
  have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
  have h2 : IsClosed (NFlag B e : Set (GA D B)) := by
    convert h1.mul_right_of_isCompact (hK.image continuous_subtype_val) using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  refine ⟨h2.locallyCompactSpace,
    (inferInstance : SecondCountableTopology (NFlag B e : Set (GA D B))), inferInstance, ?_⟩
  exact Function.Injective.countable (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))

section Invariant

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}

structure IsRatInv (ι : A.V →ₗ[D.host.E] B.V) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E)
    (Q : GA D A → GA D B → ℂ) : Prop where
  norm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e
  left : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ NFlag B e, γ ∈ GQ B → Q g (γ * n) = Q g n
  conj : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → Q (γ * g) (δ * n * δ⁻¹) = Q g n

variable {Q : GA D A → GA D B → ℂ}

end Invariant

section Integrands

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {s : GA D A → GA D B} {φ : GA D A → ℂ} {F : GA D B → ℂ}

theorem conj_arg (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) (hF : IsAutFun B F) {γ δ}
    (hγ : γ ∈ GQ A) (hδ : EmbRel B A ι δ γ) (g n y) : F (δ * n * δ⁻¹ * s (γ * g) * y) = F (n * s g * y) := by
  obtain ⟨s₀, -, hrel, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  rw [(hrel _ _).1 hδ, ← hF.left _ (hq γ hγ) (n * s₀ g * y)]
  simp only [map_mul, mul_assoc, inv_mul_cancel_left]

theorem emb_continuous (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) : Continuous s := by
  obtain ⟨s₀, hc, hrel, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  exact hc

theorem bes_inv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hι : HSpace.IsIsomEmb A B ι) (d : BesDat A B ι)
    (hs : ∀ h, EmbRel B A ι (s h) h) (hφ : IsAutFun A φ) (hF : IsAutFun B F) :
    IsRatInv ι d.e fun h n => star (φ h) * F (n * s h * (d.y : GA D B)) * star (besChar ψ d n) where
  norm δ γ h n hn := (BesselChar.besChar_conj ψ d δ γ h n hn).1
  left g n hn γ hγ hq := by
    rw [BesselChar.besChar_mul ψ d γ n hγ hn, BesselChar.besChar_rat ψ hψ.1 d γ hγ hq, one_mul, mul_assoc γ, mul_assoc γ,
      hF.left γ hq]
  conj g n hn γ hγ δ hδ := by
    rw [(BesselChar.besChar_conj ψ d δ γ hδ n hn).2, conj_arg hι hs hF hγ hδ, hφ.left γ hγ]

end Integrands

section Periods

variable {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

structure IsGood (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Prop where
  sigOK : A.SigOK
  aniso : IsAniso A
  rank : 1 < A.rank
  isom : HSpace.IsIsomEmb A B ι

structure Frame (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) where
  μ : Measure (GA D A)
  𝓕 : Set (GA D A)
  ν : Measure (NFlag B e)
  𝓝 : Set (NFlag B e)
  s : GA D A → GA D B
  vol : IsVolPair D A μ 𝓕
  unit : IsUnitN B e ν 𝓝
  emb : ∀ h, EmbRel B A ι (s h) h

variable (hg : IsGood A B ι)

include hg

omit hg

end Periods

end GlobalTheory.Per.Inhab

end
