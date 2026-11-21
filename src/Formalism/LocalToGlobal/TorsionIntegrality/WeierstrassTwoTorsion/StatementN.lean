import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def PlusZCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    derivative K (derivative K (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12)))
      - derivative K (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2
      = (2 * wpReg W - ((xPlus W xP yP).subst (expSer W) + C (W.b₂ / 12))
          - ((xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W) + C (W.b₂ / 12)))
        * (1 + X ^ 2 * (wpReg W - C (xP + W.b₂ / 12))) ^ 2

end Formalism.L2.Th1.A
