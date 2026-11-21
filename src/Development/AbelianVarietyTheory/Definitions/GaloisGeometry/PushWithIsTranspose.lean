import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Gysin

open GlobalTheory.EtC

theorem Ht.cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

theorem Ht.cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

section API

variable {q : ℕ}

theorem Ht.cast_self {E : Spc} {n i : ℤ} (hn : n = n) (hi : i = i) (x : Ht q E n i) : x.cast hn hi = x := rfl

def Ht.castHom {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : Ht q E n i →+ Ht q E n' i' where
  toFun x := x.cast hn hi
  map_zero' := Ht.cast_zero hn hi
  map_add' := Ht.cast_add hn hi

theorem Ht.castHom_apply {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) :
    Ht.castHom hn hi x = x.cast hn hi := rfl

variable {Z X : Scheme.{0}} (f : Z ⟶ X) (dZ dX : ℕ) (tZ : Ht q (sch.obj Z) (2 * dZ) dZ →+ ZMod q)
  (tX : Ht q (sch.obj X) (2 * dX) dX →+ ZMod q) (b i : ℤ)

variable {f dZ dX tZ tX b i}

end API

end GlobalTheory.EtC.Gysin

end
