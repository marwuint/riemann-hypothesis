import Formalism.CharacterColumnKernels.StatementN

open Polynomial

noncomputable section

namespace Formalism.NG

universe u

def StatBurnside : Prop :=
  ∀ (k A V : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V], IsSimpleModule A V →
    (∀ φ : V →ₗ[A] V, ∃ c : k, ∀ v, φ v = c • v) →
    Function.Surjective (fun a : A => DistribSMul.toLinearMap k V a)

def StatSplitAlg : Prop :=
  ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin P.natDegree → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = P.natDegree.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin P.natDegree → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃! φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i

def StatSplitFibre : Prop :=
  ∀ (T T' K : Type*) [CommRing T] [CommRing T'] [Algebra T T'] [Field K] (P : T[X]), P.Monic →
    ∀ (rr : Fin P.natDegree → T'), P.map (algebraMap T T') = ∏ i, (X - C (rr i)) →
      Algebra.adjoin T (Set.range rr) = ⊤ →
    ∀ (b : Module.Basis (Fin P.natDegree.factorial) T T') (x : T →+* K) (a : Fin P.natDegree → K),
      Function.Injective a → P.map x = ∏ i, (X - C (a i)) →
      ∀ c : Fin P.natDegree.factorial → K,
        (∀ φ : T' →+* K, φ.comp (algebraMap T T') = x → ∑ k, c k * φ (b k) = 0) → c = 0

end Formalism.NG
