import Formalism.YangianSpanCharacter.StatementT

namespace Formalism.YangianSpanCharacter.T

open Matrix

def pt3 {R : Type*} (M : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) R :=
  Matrix.of fun a b => M (a.1, a.2.1, b.2.2) (b.1, b.2.1, a.2.2)

def E1 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then M ik.1 jl.1 else 0

def E2 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then M ik.2 jl.2 else 0

end Formalism.YangianSpanCharacter.T
