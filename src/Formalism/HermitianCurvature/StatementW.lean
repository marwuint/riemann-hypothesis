import Formalism.YangianSpanCharacter.ExchangeGen

namespace Formalism.FourierDecayAlt.W

open Matrix Formalism.YangianSpanCharacter.T NumberField

variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]

def IsRTT (M : R → Matrix (Fin 2) (Fin 2) B) : Prop :=
  ∀ Y Y' : R, ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 (M Y') * E2 (M Y) =
    E2 (M Y) * E1 (M Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B)

def IsDet (M : R → Matrix (Fin 2) (Fin 2) B) (q : R → R) : Prop :=
  ∀ Y : R, (M (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J B * M Y = algebraMap R B (q Y) • Formalism.YangianSpanCharacter.T.J B ∧
    M Y * Formalism.YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = algebraMap R B (q Y) • Formalism.YangianSpanCharacter.T.J B

def EntriesCommute (M N : R → Matrix (Fin 2) (Fin 2) B) : Prop :=
  ∀ (Y Y' : R) (i j k l : Fin 2), M Y i j * N Y' k l = N Y' k l * M Y i j

end Formalism.FourierDecayAlt.W
