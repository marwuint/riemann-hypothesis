import Formalism.HermitianCurvature.Statement

namespace Formalism.FourierDecayAlt.P.Minors

open Matrix

variable {K : Type} [Field K]

def border {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K) (d : K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => K) (Fin.lastCases (motive := fun _ => K) d u j)
      (fun i' => Fin.lastCases (motive := fun _ => K) (v i') (A i') j) i

@[simp] lemma border_castSucc_castSucc {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (i j : Fin r) : border A v u d i.castSucc j.castSucc = A i j := by
  simp [border]

@[simp] lemma border_castSucc_last {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (i : Fin r) : border A v u d i.castSucc (Fin.last r) = v i := by
  simp [border]

@[simp] lemma border_last_castSucc {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (j : Fin r) : border A v u d (Fin.last r) j.castSucc = u j := by
  simp [border]

@[simp] lemma border_last_last {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) : border A v u d (Fin.last r) (Fin.last r) = d := by
  simp [border]

variable [Fintype K]

end Formalism.FourierDecayAlt.P.Minors

