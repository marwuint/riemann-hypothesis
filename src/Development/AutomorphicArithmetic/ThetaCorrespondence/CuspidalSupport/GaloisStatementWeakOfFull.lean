import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

namespace UpperTheory.Lit.Car

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IneAb {w : PlE H} (y : A.LP w) : Prop :=
  ∀ σ ∈ ⁅Ine (F := H.E) (N.plOm.1 w), Ine (F := H.E) (N.plOm.1 w)⁆, A.inePol y σ = (X - 1) ^ A.lpDim y

structure RelA {w : PlE H} (x y : A.LP w) : Prop where
  dim : A.lpDim x = A.lpDim y
  mono : A.mono0 y → A.mono0 x
  ine : IneAb N A y → ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol x σ = A.inePol y σ

structure Cusp {w : PlE H} (x y : A.LP w) : Prop where
  rel : RelA N A x y
  temp : Odd (A.lpDim y) → ∀ s : ℝ, A.tempered (A.lpTw y s) → A.tempered (A.lpTw x s)
  one : A.lpDim y = 1 → x = y

variable {N A}

theorem RelA.refl {w : PlE H} (x : A.LP w) : RelA N A x x := ⟨rfl, id, fun _ _ _ => rfl⟩

theorem RelA.of_eq {w : PlE H} {x y : A.LP w} (e : x = y) : RelA N A x y := e ▸ RelA.refl x

theorem Cusp.of_eq {w : PlE H} {x y : A.LP w} (e : x = y) : Cusp N A x y :=
  ⟨RelA.of_eq e, fun _ _ h => e ▸ h, fun _ => e⟩

theorem comm_le_ine (w : PlE H) :
    ⁅Ine (F := H.E) (N.plOm.1 w), Ine (F := H.E) (N.plOm.1 w)⁆ ≤ Ine (F := H.E) (N.plOm.1 w) :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem eq_pow_of_mul {p q : ℂ[X]} (hp : p.Monic) {n : ℕ} (h : p * q = (X - 1) ^ n) : p = (X - 1) ^ p.natDegree := by
  have hirr : Prime (X - C (1 : ℂ)) := prime_X_sub_C 1
  have hd : p ∣ (X - C (1 : ℂ)) ^ n := ⟨q, by simpa using h.symm⟩
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow hirr n).1 hd
  have e : p = (X - C (1 : ℂ)) ^ k := eq_of_monic_of_associated hp ((monic_X_sub_C 1).pow k) hk
  have : p.natDegree = k := by rw [e, natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [this, e]; simp

theorem inePol_char_unr (hLP : TieLP N A) {w : PlE H} (a c : A.LP w) (hc : A.lpDim c = 1) (hu : A.unr c) :
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.lpChar a c) σ = A.inePol a σ := fun σ hσ => by
  have e : A.inePol c σ = X - C 1 := by rw [((A.unr_iff_ine c).1 hu).2 σ hσ, hc]; simp
  rw [((hLP w a a c c 0 hc hc).2.2.2.2.2 σ hσ).2 1 e, scaleRoots_one]

variable (N A)

end UpperTheory.Lit.Car
