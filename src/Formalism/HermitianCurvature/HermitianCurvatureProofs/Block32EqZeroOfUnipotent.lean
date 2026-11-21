import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Minors

namespace Formalism.FourierDecayAlt.P.S3x9

open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)

theorem block31_add {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x + y) = b31 x + b31 y := rfl

theorem block31_sub {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x - y) = b31 x - b31 y := rfl

theorem block31_smul {A : Type} [CommRing A] {r k : ℕ} (c : A) (x : Matrix (Idx r k) (Idx r k) A) :
    b31 (c • x) = c • b31 x := rfl

theorem block32_map {A B : Type} {r k : ℕ} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl

def lowerLeftBlockMatrix {A : Type} [Zero A] (r k : ℕ) (Y : Matrix (Fin r) (Fin r) A) : Matrix (Idx r k) (Idx r k) A :=
  Matrix.of fun i j =>
    match i, j with
    | Sum.inr (Sum.inr a), Sum.inl b => Y a b
    | _, _ => 0

theorem block31_lowerLeftBlockMatrix {A : Type} [Zero A] (r k : ℕ) (Y : Matrix (Fin r) (Fin r) A) :
    b31 (lowerLeftBlockMatrix r k Y) = Y := rfl

end Formalism.FourierDecayAlt.P.S3x9

