import Formalism.LocalRingCardinality.SpanPowerMembership.NStageTrivialCharacterCoeffEq

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000 in

structure TwCore (R : Ranks) (H : Host R) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (N : NData R H what₂) where
  cc : N.Om ≃+* N.Om
  cc_cm : IsCMConjOm H.E N.Om cc
  Tw : Type
  l : Tw → ℕ
  [lPrime : ∀ i, Fact (l i).Prime]
  O0 : Tw → Type
  [crO0 : ∀ i, CommRing (O0 i)]
  [twistBaseCoefficientRing_isDomain : ∀ i, IsDomain (O0 i)]
  [twistBaseCoefficientRing_isDVR : ∀ i, IsDiscreteValuationRing (O0 i)]
  [algO0 : ∀ i, Algebra ℤ_[l i] (O0 i)]
  [twistBaseCoefficientRing_finite_padic : ∀ i, Module.Finite ℤ_[l i] (O0 i)]
  twistBaseCoefficientRing_residueField_finite : ∀ i, Finite (IsLocalRing.ResidueField (O0 i))
  [topO0 : ∀ i, TopologicalSpace (O0 i)]
  [twistBaseCoefficientRing_topologicalRing : ∀ i, IsTopologicalRing (O0 i)]
  twistBaseCoefficientRing_isAdic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O0 i))
  emb0 : ∀ i, LL0 →+* FractionRing (O0 i)
  emb0b : ∀ i, LL0 →+* FractionRing (O0 i)
  restX_coefficientEmbedding_conj : ∀ i (x y : LL0), (y : what₂.LL) = star (x : what₂.LL) → emb0b i x = emb0 i y
  O : Tw → Type
  [crO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]
  [dvrO : ∀ i, IsDiscreteValuationRing (O i)]
  [algO : ∀ i, Algebra (O0 i) (O i)]
  O_inj : ∀ i, Function.Injective (algebraMap (O0 i) (O i))
  O_l : ∀ i, ((l i : ℕ) : O i) ∈ IsLocalRing.maximalIdeal (O i)
  [topO : ∀ i, TopologicalSpace (O i)]
  [trO : ∀ i, IsTopologicalRing (O i)]
  O_adic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O i))
  resO_ac : ∀ i, IsAlgClosed (IsLocalRing.ResidueField (O i))
  O_complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)
  Ok : Tw → ℕ → Type
  [crOk : ∀ i k, CommRing (Ok i k)]
  [domOk : ∀ i k, IsDomain (Ok i k)]
  [dvrOk : ∀ i k, IsDiscreteValuationRing (Ok i k)]
  [algOk : ∀ i k, Algebra (O i) (Ok i k)]
  Ok_inj : ∀ i k, Function.Injective (algebraMap (O i) (Ok i k))
  Ok_fin : ∀ i k, Module.Finite (O i) (Ok i k)
  zk : ∀ i k, (Ok i k)ˣ
  zk_prim : ∀ i k, IsPrimitiveRoot ((zk i k : Ok i k)) (l i ^ k)
  Ok_gen : ∀ i k (x : FractionRing (Ok i k)), ∃ p : Polynomial (O i), ∃ d : O i, d ≠ 0 ∧
    x * algebraMap (Ok i k) (FractionRing (Ok i k)) (algebraMap (O i) (Ok i k) d) =
      algebraMap (Ok i k) (FractionRing (Ok i k)) (Polynomial.aeval (zk i k : Ok i k) p)
  pD : Tw → Finset (HeightOneSpectrum (𝓞 H.E))
  pD_eq : ∀ i, (pD i : Set (HeightOneSpectrum (𝓞 H.E))) =
    placesOver H.E (if l i = H.pde then H.pde' else H.pde)
  delta : ∀ i, Formalism.ConjugateSelfDual.G H.E N.Om →* (O0 i)ˣ
  delta_open : ∀ i, IsOpen ((delta i).ker : Set (Formalism.ConjugateSelfDual.G H.E N.Om))
  delta_anti : ∀ i, AntiHom cc (delta i)
  delta_ram : ∀ i, RamExactly (delta i) ↑(pD i)
  delta_15 : ∀ i, ∀ v ∈ pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    Nat.card ((Ine (F := H.E) A).map (delta i)) = 15
  delta_tame : ∀ i, ∀ v ∈ pD i, Ideal.absNorm v.asIdeal % 15 = 1
  RCG : Tw → Finset (HeightOneSpectrum (𝓞 H.E)) → Type
  [grpRCG : ∀ i Q, CommGroup (RCG i Q)]
  [finRCG : ∀ i Q, Fintype (RCG i Q)]
  RCG_l : ∀ i Q (x : RCG i Q), ∃ n : ℕ, x ^ (l i ^ n) = 1
  art : ∀ i Q, Formalism.ConjugateSelfDual.G H.E N.Om →* RCG i Q
  art_surj : ∀ i Q, Function.Surjective (art i Q)
  art_cont : ∀ i Q, IsOpen ((art i Q).ker : Set (Formalism.ConjugateSelfDual.G H.E N.Om))
  art_anti : ∀ i Q, AntiHom cc (art i Q)
  art_unr : ∀ i Q v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, art i Q σ = 1
  art_univ : ∀ i Q, (∀ v ∈ Q, v ∉ placesOver H.E (l i)) → ∀ (A' : Type) [CommGroup A'] [Finite A'],
    (∀ x : A', ∃ n : ℕ, x ^ (l i ^ n) = 1) → ∀ φ : Formalism.ConjugateSelfDual.G H.E N.Om →* A',
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G H.E N.Om)) → AntiHom cc φ →
    (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, φ σ = 1) →
    ∃ f : RCG i Q →* A', f.comp (art i Q) = φ
  res : ∀ i (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (RCG i Q →* RCG i Q')
  res_art : ∀ i Q Q' (h : Q' ⊆ Q), (res i Q Q' h).comp (art i Q) = art i Q'
  iC : ∀ i, FractionRing (O i) →+* ℂ_[l i]
  iC_int : ∀ i (x : FractionRing (O i)), ‖iC i x‖ ≤ 1 ↔ x ∈ (algebraMap (O i) (FractionRing (O i))).range
  br : ∀ i (w : HeightOneSpectrum (𝓞 H.E)), w ∈ placesOver H.E (l i) →
    LocBridge (l i) H.E N.Om (Dec (F := H.E) (N.plOm.1 w)) (O0 i)

  br_ind : ∀ i (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (l i)) (x : N.Om),
    x ∈ N.plOm.1 w ↔ ‖(br i w hw).j x‖ ≤ 1
  cover : ∀ p : ℕ, p.Prime → ∀ w : HeightOneSpectrum (𝓞 ↥LL0), ((p : ℕ) : 𝓞 ↥LL0) ∈ w.asIdeal →
    ∃ i, l i = p ∧ ∀ x : 𝓞 ↥LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (O0 i),
      algebraMap (O0 i) (FractionRing (O0 i)) y = emb0 i (x : ↥LL0)

attribute [instance] TwCore.lPrime TwCore.crO0 TwCore.twistBaseCoefficientRing_isDomain TwCore.twistBaseCoefficientRing_isDVR TwCore.algO0 TwCore.twistBaseCoefficientRing_finite_padic TwCore.topO0 TwCore.twistBaseCoefficientRing_topologicalRing TwCore.crO TwCore.domO TwCore.dvrO TwCore.algO TwCore.topO TwCore.trO TwCore.crOk TwCore.domOk TwCore.dvrOk TwCore.algOk TwCore.grpRCG TwCore.finRCG

namespace TwCore

end TwCore

end Formalism.BasicNotions.Examples₂
