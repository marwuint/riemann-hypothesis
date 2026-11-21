import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.K.GA

variable (K : Type) [Field K] [NumberField K]

def nx : Multiplicative K →* GL (Fin 2) K where
  toFun x := ⟨!![1, x.toAdd; 0, 1], !![1, -x.toAdd; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def nU : Subgroup (GL (Fin 2) K) := (nx K).range

abbrev NQ : Type := Quotient (QuotientGroup.rightRel (nU K))

def b1M : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun γ := !![γ 0 0, γ 0 1, 0; γ 1 0, γ 1 1, 0; 0, 0, 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def b2M : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun γ := !![1, 0, 0; 0, γ 0 0, γ 0 1; 0, γ 1 0, γ 1 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def e1 : GL (Fin 2) K →* GL (Fin 3) K := Units.map (b1M K)

def e2 : GL (Fin 2) K →* GL (Fin 3) K := Units.map (b2M K)

def sw : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

variable {K}

def vS (W : G3K K → ℂ) (g : G3K K) : ℂ := ∑' q : NQ K, W (diaK (e2 K q.out * sw K) * g)

def lowM (c : 𝔸[K]) : G3K K :=
  ⟨!![1, 0, 0; c, 1, 0; 0, 0, 1], !![1, 0, 0; -c, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def ctY (f : G3K K → ℂ) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 2), f (uni 0 (y 0) (y 1) * g) ∂vecMeasure K (Fin 2)

def ctY' (f : G3K K → ℂ) (g : G3K K) : ℂ :=
  ∫ y in vecDomain K (Fin 2), f (lowM (y 0) * uni 0 0 (y 1) * g) ∂vecMeasure K (Fin 2)

variable (K)

def Cusp : Prop := ∀ f : G3K K → ℂ, Continuous f → IsLeftInvariant f → (∀ g, ctY f g = 0) → (∀ g, ctY' f g = 0) →
  IsCuspidal f

end Ad3.K.GA
