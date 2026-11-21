import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

private lemma dg_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.dg n i : 𝓞 E) : E) = ((A.dg n i : 𝓞 E) : E) := by
  have h : A.bar (A.dg n i) = A.dg n i := by
    unfold Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

private lemma hd_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.hd n i : 𝓞 E) : E) = ((A.hd n i : 𝓞 E) : E) := by
  have h : A.bar (A.hd n i) = A.hd n i := by
    unfold Arith.hd Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

private lemma sym_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    ((A.H n).map (cj E))⁻¹ * ((Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)).map (cj E))ᵀ * (A.H n).map (cj E) =
      Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
  have hH : (A.H n).map (cj E) = A.H n := by
    unfold Arith.H
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact hd_cj A n i
  have hD : (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)).map (cj E) =
      Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact dg_cj A n i
  have hu : IsUnit (A.H n).det := (A.det_ne n).isUnit
  have hc : (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)) * A.H n =
      A.H n * Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
    unfold Arith.H
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [hH, hD, Matrix.diagonal_transpose, Matrix.mul_assoc, hc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

