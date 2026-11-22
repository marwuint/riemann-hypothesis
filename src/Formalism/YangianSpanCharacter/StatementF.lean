import Formalism.YangianSpanCharacter.ExchangeGen
import Formalism.YangianSpanCharacter.StatementY

namespace Formalism.YangianSpanCharacter.F

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y

def blk {A : Type*} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) (i j : Fin 2) :
    Matrix (Fin 2) (Fin 2) A :=
  Matrix.of fun k l => M (i, k) (j, l)

def sc {A : Type*} [Ring A] (x : A) : Matrix (Fin 2) (Fin 2) A := Matrix.diagonal fun _ => x

def MinusFrame : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y Yb : 𝕜, Y ∈ S → Y + 1 ∈ S → Yb ∈ S → Yb + 1 ∈ S → Yb - 1 ∈ S →
      Yb - Y ≠ 0 → Yb - Y - 1 ≠ 0 →
      let d := Yb - Y
      let tn := ((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) *
        E1 (t Y)
      let τn : Matrix (Fin 2) (Fin 2) A := !![d • t Y 1 1, 0; -t Y 0 1, (d - 1) • t Y 1 1]
      let Ln : Matrix (Fin 2) (Fin 2) A :=
        !![lf t τinv Y, 0; -((d - 1)⁻¹ • hf τinv q Y), lf t τinv Y]
      let Gb : Matrix (Fin 2) (Fin 2) A := !![1, 0; mf t τinv Yb, 1]
      blk tn 1 1 = (d - 1)⁻¹ • τn ∧
      blk tn 1 0 = (d - 1)⁻¹ • !![d • t Y 1 0, 0; -t Y 0 0, (d - 1) • t Y 1 0] ∧
      τn * Ln = !![d • t Y 1 0, 0; -t Y 0 0, (d - 1) • t Y 1 0] ∧
      Gb * τn = !![d • t Y 1 1, 0; 0, (d - 1) • t Y 1 1] * Gb ∧
      Gb * Ln = !![lf t τinv Y, 0; -((d - 1)⁻¹ • hf τinv q (Yb - 1)), lf t τinv Y] * Gb

end Formalism.YangianSpanCharacter.F
