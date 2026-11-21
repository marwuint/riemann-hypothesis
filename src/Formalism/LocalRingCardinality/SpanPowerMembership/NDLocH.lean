import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

def DeltaGap {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] (cc : Ω ≃+* Ω) (p : ℕ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (δ : Formalism.ConjugateSelfDual.G H.E Ω →* Multiplicative (ZMod N)),
    IsOpen (δ.ker : Set (Formalism.ConjugateSelfDual.G H.E Ω)) ∧ AntiHom cc δ ∧ RamExactly δ (placesOver H.E p) ∧
    ∀ v ∈ placesOver H.E p, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      Nat.card ((Ine (F := H.E) A).map δ) = 15

structure RcgAt {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] (cc : Ω ≃+* Ω) (l : ℕ) : Type 1 where
  RCG : Finset (HeightOneSpectrum (𝓞 H.E)) → Type
  [grpRCG : ∀ Q, CommGroup (RCG Q)]
  [finRCG : ∀ Q, Fintype (RCG Q)]
  RCG_l : ∀ Q (x : RCG Q), ∃ n : ℕ, x ^ (l ^ n) = 1
  art : ∀ Q, Formalism.ConjugateSelfDual.G H.E Ω →* RCG Q
  art_surj : ∀ Q, Function.Surjective (art Q)
  art_cont : ∀ Q, IsOpen ((art Q).ker : Set (Formalism.ConjugateSelfDual.G H.E Ω))
  art_anti : ∀ Q, AntiHom cc (art Q)
  art_unr : ∀ Q v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, art Q σ = 1
  art_univ : ∀ Q, (∀ v ∈ Q, v ∉ placesOver H.E l) → ∀ (A' : Type) [CommGroup A'] [Finite A'],
    (∀ x : A', ∃ n : ℕ, x ^ (l ^ n) = 1) → ∀ φ : Formalism.ConjugateSelfDual.G H.E Ω →* A',
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G H.E Ω)) → AntiHom cc φ →
    (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, φ σ = 1) →
    ∃ f : RCG Q →* A', f.comp (art Q) = φ
  res : ∀ (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (RCG Q →* RCG Q')
  res_art : ∀ Q Q' (h : Q' ⊆ Q), (res Q Q' h).comp (art Q) = art Q'

attribute [instance] RcgAt.grpRCG RcgAt.finRCG

namespace TwB

variable {R : Ranks} (H : Host R) (F : Type) [Field F] [NumberField F]
  {Ω : Type} [Field Ω] [Algebra H.E Ω] {cc : Ω ≃+* Ω}

def pOf (l : ℕ) : ℕ := if l = H.pde then H.pde' else H.pde

variable (dg : ∀ l : ℕ, DeltaGap H cc (pOf H l))

def NOf (l : ℕ) : ℕ := (dg l).choose

instance (l : ℕ) : NeZero (NOf H dg l) := ⟨(dg l).choose_spec.choose.ne'⟩

variable (l : ℕ) [hl : Fact l.Prime]

end TwB

end Formalism.BasicNotions.Examples₂
