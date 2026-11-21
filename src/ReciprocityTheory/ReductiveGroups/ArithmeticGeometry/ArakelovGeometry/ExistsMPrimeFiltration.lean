import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HilbertMultidegreePieceDivisorSum

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem exists_mPrimeFiltration {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = ⊤ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc :=
  exists_primeFiltration_of_isMultiHomogIdeal J hJ

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
