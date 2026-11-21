import Formalism.SatakeDualWeyl.StatementG
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Gen

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem gLoc_bc_coe (e : A →+* L) (g : GL n A) :
    ((bc (n := n) e g : GL n L) : Matrix n n L) = (g : Matrix n n A).map e := rfl

theorem gLoc_mem_one_iff (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L)
    (he : ∀ x, e (σA x) = σL (e x)) (g : GL n A) :
    g ∈ UJ σA (1 : Matrix n n A) ↔ bc (e : A →+* L) g ∈ UJ σL (1 : Matrix n n L) := by
  set f : A →+* L := (e : A →+* L)
  have hf : Function.Injective f := e.injective
  have hc : (RingHom.mapMatrix f) (cT σA (g : Matrix n n A)) =
      cT σL (RingHom.mapMatrix f (g : Matrix n n A)) := by
    ext i j
    simp [cT, f, he]
  show cT σA (g : Matrix n n A) * 1 * (g : Matrix n n A) = 1 ↔
    cT σL (RingHom.mapMatrix f (g : Matrix n n A)) * 1 * RingHom.mapMatrix f (g : Matrix n n A) = 1
  rw [← hc, ← map_one (RingHom.mapMatrix f), ← map_mul, ← map_mul, map_one]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    apply Matrix.map_injective hf
    simpa [RingHom.mapMatrix_apply] using h

theorem gLoc_conj_iff (σL : L →+* L) (J : Matrix n n L) (P : GL n L)
    (hP : cT σL (P : Matrix n n L) * (P : Matrix n n L) = J) (g : GL n L) :
    g ∈ UJ σL (1 : Matrix n n L) ↔ P⁻¹ * g * P ∈ UJ σL J := by
  set p : Matrix n n L := (P : Matrix n n L)
  set q : Matrix n n L := ((P⁻¹ : GL n L) : Matrix n n L)
  set G : Matrix n n L := (g : Matrix n n L)
  have hpq : p * q = 1 := by
    simp only [p, q]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqp : q * p = 1 := by
    simp only [p, q]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have cq : cT σL q * cT σL p = 1 := by rw [← cT_mul, hpq, cT_one]
  have cancel : ∀ X, cT σL q * (cT σL p * X * p) * q = X := fun X => by
    calc cT σL q * (cT σL p * X * p) * q = (cT σL q * cT σL p) * X * (p * q) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [cq, hpq, Matrix.one_mul, Matrix.mul_one]
  have inj : ∀ X Y, cT σL p * X * p = cT σL p * Y * p → X = Y := fun X Y h => by
    rw [← cancel X, ← cancel Y, h]
  have E : cT σL (q * G * p) * (cT σL p * p) * (q * G * p) = cT σL p * (cT σL G * G) * p := by
    rw [cT_mul, cT_mul]
    calc cT σL p * (cT σL G * cT σL q) * (cT σL p * p) * (q * G * p)
        = cT σL p * (cT σL G * ((cT σL q * cT σL p) * (p * q)) * G) * p := by
          simp only [Matrix.mul_assoc]
      _ = cT σL p * (cT σL G * G) * p := by rw [cq, hpq, Matrix.one_mul, Matrix.mul_one]
  show cT σL G * 1 * G = 1 ↔
    cT σL (((P⁻¹ * g * P : GL n L)) : Matrix n n L) * J * ((P⁻¹ * g * P : GL n L) : Matrix n n L) = J
  rw [show (((P⁻¹ * g * P : GL n L)) : Matrix n n L) = q * G * p by simp only [Units.val_mul, p, q, G]]
  rw [← hP, E, Matrix.mul_one]
  constructor
  · intro h
    rw [h, Matrix.mul_one]
  · intro h
    exact inj _ _ (by rw [h, Matrix.mul_one])

end Gen

section Main

variable {A L : Type} [CommRing A] [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

def gLoc_hom (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A)) :
    H →* GU σL m where
  toFun x := ⟨P⁻¹ * bc (e : A →+* L) (x : GL (Fin m) A) * P,
    (gLoc_conj_iff σL _ P hP _).1 ((gLoc_mem_one_iff σA σL e he _).1 ((hH _).1 x.2))⟩
  map_one' := by
    apply Subtype.ext
    show P⁻¹ * bc (e : A →+* L) (1 : GL (Fin m) A) * P = 1
    rw [map_one, mul_one, inv_mul_cancel]
  map_mul' a b := by
    apply Subtype.ext
    show P⁻¹ * bc (e : A →+* L) ((a : GL (Fin m) A) * (b : GL (Fin m) A)) * P =
      (P⁻¹ * bc (e : A →+* L) (a : GL (Fin m) A) * P) * (P⁻¹ * bc (e : A →+* L) (b : GL (Fin m) A) * P)
    rw [map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem gLoc_hom_apply (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A))
    (x : H) :
    ((gLoc_hom σA σL e he P hP H hH x : GU σL m) : GL (Fin m) L) =
      P⁻¹ * bc (e : A →+* L) (x : GL (Fin m) A) * P := rfl

end Main

end Formalism.UG.P
