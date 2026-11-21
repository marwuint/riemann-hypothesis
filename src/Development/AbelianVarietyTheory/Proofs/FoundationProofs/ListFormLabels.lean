import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

open Polynomial

noncomputable section

namespace GlobalTheory.Proof.ListFormLabels

open Formalism.BasicNotions

def ListFormAt (D : D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (∃ L : List (ℕ × ℕ × Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k))),
      (L.map fun p => (p.1, p.2.1) : Multiset (ℕ × ℕ)) = D.ntypes.bc σ ∧
      (∀ p ∈ L, Multiset.card p.2.2 = p.1 ∧ p.2.2.map (fun x => x ^ D.host.g k) = p.2.2) ∧
      Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v) = (L.map fun p => p.2.1 • p.2.2).sum) ∧
    (D.ntypes.cuspidal σ →
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ D.host.g k →
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w) x))).prod ∧
      ∃ φ : Formalism.MainNotions.N.GE D.nd,
        D.ntypes.rbar σ w (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ w (D.ntypes.tg k v) ^ D.host.g k)

theorem listForm_iff_forall (D : D7) : Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D ↔ ∀ σ k v, ListFormAt D σ k v := Iff.rfl

end GlobalTheory.Proof.ListFormLabels
