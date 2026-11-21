import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA

def nx : Multiplicative ℚ →* GL (Fin 2) ℚ where
  toFun x := ⟨!![1, x.toAdd; 0, 1], !![1, -x.toAdd; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def nU : Subgroup (GL (Fin 2) ℚ) := nx.range

abbrev NQ : Type := Quotient (QuotientGroup.rightRel nU)

def b1M : Matrix (Fin 2) (Fin 2) ℚ →* Matrix (Fin 3) (Fin 3) ℚ where
  toFun γ := !![γ 0 0, γ 0 1, 0; γ 1 0, γ 1 1, 0; 0, 0, 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def b2M : Matrix (Fin 2) (Fin 2) ℚ →* Matrix (Fin 3) (Fin 3) ℚ where
  toFun γ := !![1, 0, 0; 0, γ 0 0, γ 0 1; 0, γ 1 0, γ 1 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def e1 : GL (Fin 2) ℚ →* GL (Fin 3) ℚ := Units.map b1M

def e2 : GL (Fin 2) ℚ →* GL (Fin 3) ℚ := Units.map b2M

def sw : GL (Fin 3) ℚ :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def vS (W : G3 → ℂ) (g : G3) : ℂ := ∑' q : NQ, W (dia (e2 q.out * sw) * g)

def lowM (c : 𝔸[ℚ]) : G3 :=
  ⟨!![1, 0, 0; c, 1, 0; 0, 0, 1], !![1, 0, 0; -c, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def ctY (f : G3 → ℂ) (g : G3) : ℂ :=
  ∫ y in vecDomain ℚ (Fin 2), f (uni 0 (y 0) (y 1) * g) ∂vecMeasure ℚ (Fin 2)

def ctY' (f : G3 → ℂ) (g : G3) : ℂ :=
  ∫ y in vecDomain ℚ (Fin 2), f (lowM (y 0) * uni 0 0 (y 1) * g) ∂vecMeasure ℚ (Fin 2)

def Cusp : Prop := ∀ f : G3 → ℂ, Continuous f → IsLeftInvariant f → (∀ g, ctY f g = 0) → (∀ g, ctY' f g = 0) →
  IsCuspidal f

end Ad3.GA
