import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.S3x8

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

theorem block11_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b11 (x.map f) = (b11 x).map f := rfl

theorem block12_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b12 (x.map f) = (b12 x).map f := rfl

theorem block13_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b13 (x.map f) = (b13 x).map f := rfl

theorem block21_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b21 (x.map f) = (b21 x).map f := rfl

theorem block22_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b22 (x.map f) = (b22 x).map f := rfl

theorem block23_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b23 (x.map f) = (b23 x).map f := rfl

theorem block31_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b31 (x.map f) = (b31 x).map f := rfl

theorem block32_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl

theorem block33_map {B : Type} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b33 (x.map f) = (b33 x).map f := rfl

end Blocks

end Formalism.FourierDecayAlt.P.S3x8

