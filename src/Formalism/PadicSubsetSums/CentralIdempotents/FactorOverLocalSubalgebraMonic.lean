import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

noncomputable section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

def ResidueCharpolyEq : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (G : Type) (n : ℕ) (r : X' → G → Matrix (Fin n) (Fin n) O),
    (∀ (g : G) (j : ℕ), (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T) →
    ∀ (x y : X') (g : G),
      Matrix.charpolyRev ((r x g).map (IsLocalRing.residue O)) =
        Matrix.charpolyRev ((r y g).map (IsLocalRing.residue O)) ∧
      ((r x g).map (IsLocalRing.residue O)).charpoly =
        ((r y g).map (IsLocalRing.residue O)).charpoly

def GoodCuspidalOne : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [Nonempty P] (r : ℕ) (f : P → k[X]) (I : Type) [Fintype I]
    (n d : I → ℕ) (h : P → I → k[X]), 1 ≤ r →
    (∀ v, (f v).natDegree = r) → (∀ v, Squarefree (f v)) → (∀ v, f v = ∏ i, h v i ^ d i) →
    (∀ v i, (h v i).natDegree = n i) → (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ d i) →
    (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ r ∧ ∀ v, ∃ g : k[X], g ∣ f v ∧ g.natDegree = a) →
    Fintype.card I = 1 ∧ ∀ i, d i = 1 ∧ n i = r

def CharpolyOverSubalgebra : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O))
    (n : ℕ) (M : X' → Matrix (Fin n) (Fin n) O),
    (∀ j : ℕ, (fun x => (Matrix.charpolyRev (M x)).coeff j) ∈ T) →
    ∃ F : T[X], F.Monic ∧ ∀ x, F.map (ev T x) = (M x).charpoly

def FactorOverLocalSubalgebraMonic : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (t : ℕ) (c : O) (F : T[X]) (s : X' → O[X]), F.Monic →
    (∀ x, F.map (ev T x) = s x * (X - C c) ^ t) → (∀ x, IsUnit ((s x).eval c)) →
    ∃ P : T[X], P.Monic ∧ F = P * (X - C (algebraMap O T c)) ^ t ∧
      IsUnit (P.eval (algebraMap O T c)) ∧ ∀ x, P.map (ev T x) = s x

def FactorAnnihilatorFamily : Prop :=
  ∀ (O K : Type) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K],
    Function.Injective (algebraMap O K) →
    ∀ (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)), IsLocalRing T →
    ∀ (V : X' → Type) [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]
      [∀ x, FiniteDimensional K (V x)] (A B : ∀ x, Submodule K (V x))
      (γ₀ γ : ∀ x, Module.End K (V x)) (c cγ : O) (t : ℕ) (F : T[X]),
    (∀ x, (F.map (ev T x)).map (algebraMap O K) = (γ₀ x).charpoly) →
    (∀ x, IsCompl (A x) (B x)) → (∀ x, ∀ v ∈ A x, γ₀ x v ∈ A x) → (∀ x, ∀ v ∈ A x, γ x v ∈ A x) →
    (∀ x, ∀ v ∈ B x, γ₀ x v = algebraMap O K c • v) →
    (∀ x, ∀ v ∈ B x, γ x v = algebraMap O K cγ • v) →
    (∀ x, Module.finrank K (B x) = t) →
    (∀ x, ((F.map (ev T x)).map (IsLocalRing.residue O)).rootMultiplicity
      (IsLocalRing.residue O c) = t) →
    ∃ P : T[X], P.Monic ∧ F = P * (X - C (algebraMap O T c)) ^ t ∧
      IsUnit (P.eval (algebraMap O T c)) ∧
      ∀ x, (aeval (γ₀ x) ((P.map (ev T x)).map (algebraMap O K))) *
        (γ x - algebraMap K (Module.End K (V x)) (algebraMap O K cγ)) = 0

end Formalism.IrreducibleCountingLemmas.Z
