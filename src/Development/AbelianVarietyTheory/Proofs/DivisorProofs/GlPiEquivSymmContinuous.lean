import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ShiftTw
open Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

def matPiEquiv (S : Type) [CommRing S] (n k : ℕ) :
    Matrix (Fin n) (Fin n) (Fin k → S) ≃+* (Fin k → Matrix (Fin n) (Fin n) S) where
  toFun M i := (Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix M
  invFun N := Matrix.of fun a b i => N i a b
  left_inv M := by ext a b i; rfl
  right_inv N := by funext i; ext a b; rfl
  map_mul' M N := by funext i; exact map_mul ((Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix) M N
  map_add' M N := by funext i; exact map_add ((Pi.evalRingHom (fun _ : Fin k => S) i).mapMatrix) M N

def glPiEquiv {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S)) :
    GL (Fin n) R ≃* (Fin (d + 1) → GL (Fin n) S) :=
  (Units.mapEquiv (e.mapMatrix.trans (matPiEquiv S n (d + 1))).toMulEquiv).trans MulEquiv.piUnits

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

end GlobalTheory.LKRes
