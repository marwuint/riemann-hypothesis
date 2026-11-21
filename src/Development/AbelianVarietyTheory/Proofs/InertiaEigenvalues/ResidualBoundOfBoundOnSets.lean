import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualBoundAdmissible

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open GlobalTheory.IndefiniteRowSideFullHecke.ResidualBoundAdmissible

namespace GlobalTheory.TwSys.ResidualCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isConjPl_unique {P v v' : PlE D.host} (h : IsConjPl D.host P v) (h' : IsConjPl D.host P v') : v = v' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

variable (bkP : BKPh X)

def AtLevel₁ (i : X.Tw) (T : Set (X.Sig i)) (R n M : ℕ) : Prop :=
  ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
        Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ n ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤ 0

def AtLevel₂ (i : X.Tw) (T : Set (X.Sig i)) (R n M : ℕ) : Prop :=
  ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host))
    (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))), AdmFam X i M H S d →
    ∀ z : GE N, IsTameInertiaElementAtTwistPrime X i z →
    ∀ H' : Subgroup (GE N), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host),
      ∃ (P : Fin R ⊕ Fin R → PlE D.host) (Q : Finset (PlE D.host)),
        (∀ q, AdmPl H S (P q)) ∧
        SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
        Steps X i M H' z P (fun q => d (P q)) ∧
        IsQ P Q ∧
        ∀ s ∈ T, ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
          Computes bkP i s M (fun q => d (P q)) Q Φ → OrdLE X i M (Fin R ⊕ Fin R) n Φ.det

theorem ordBound_zero_iff (i : X.Tw) : OrdBound bkP i 0 ↔
    ∀ T : Set (X.Sig i), (∀ s ∈ T, GalHyp bkP i s) → ∃ R n M₀ : ℕ, ∀ M, M₀ ≤ M → AtLevel₁ bkP i T R n M := Iff.rfl

theorem residualBoundOn_iff (i : X.Tw) (T : Set (X.Sig i)) : ResidualBoundOn bkP i T ↔
    (nu X i = 0 → (∀ s ∈ T, GalHyp bkP i s) →
      ∃ R : ℕ, ∀ M : ℕ, 4 * D.R.r * R + 1 < X.l i ^ M → AtLevel₂ bkP i T R (4 * D.R.r * R) M) := Iff.rfl

end GlobalTheory.TwSys.ResidualCompare

end
