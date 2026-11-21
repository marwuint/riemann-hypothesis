import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbIndepField

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

lemma qb_card_Idx {M : GLMod n} (CF : ColFam M) : Fintype.card (qb_Idx CF) = Fintype.card M.ι := by
  rw [Fintype.card_sigma, CF.rank]
  refine sum_congr rfl fun j _ => ?_
  rw [dMu, Nat.card_eq_fintype_card]

def qb_e {M : GLMod n} (CF : ColFam M) : M.ι ≃ qb_Idx CF := Fintype.equivOfCardEq (qb_card_Idx CF).symm

def qb_N {M : GLMod n} (CF : ColFam M) : Matrix M.ι M.ι ℤ :=
  Matrix.of fun k i => CF.vec (qb_e CF k).1 (qb_e CF k).2.1 i

lemma qb_N_row {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] :
    ((qb_N CF).map (Int.castRingHom R)).row = qb_vecF CF R ∘ qb_e CF := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
