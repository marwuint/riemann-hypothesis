import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DifferentiableAtChart

open NumberField IsDedekindDomain GlobalTheory.CuspNF Matrix Topology

namespace GlobalTheory.CuspNF.KprOpen

theorem mem_map_ker {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n] (S : Subring A) (m : S) (g : GL n A)
    (h1 : ∀ i j, (g : Matrix n n A) i j ∈ S) (h2 : ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S)
    (h3 : ∀ i j, ∃ y ∈ S, y * (m : A) = (g : Matrix n n A) i j - (1 : Matrix n n A) i j) :
    g ∈ (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {m}))).ker.map (GeneralLinearGroup.map S.subtype) := by
  let P : Matrix n n S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let Q : Matrix n n S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hinj : Function.Injective (S.subtype.mapMatrix : Matrix n n S →+* Matrix n n A) := fun x y h => by
    ext i j
    exact congrFun (congrFun h i) j
  have hP : S.subtype.mapMatrix P = (g : Matrix n n A) := rfl
  have hQ : S.subtype.mapMatrix Q = ((g⁻¹ : GL n A) : Matrix n n A) := rfl
  let u : GL n S := ⟨P, Q, hinj (by rw [map_mul, hP, hQ, map_one, Units.mul_inv]),
    hinj (by rw [map_mul, hP, hQ, map_one, Units.inv_mul])⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  refine Units.ext ?_
  ext i j
  obtain ⟨y, hy, e⟩ := h3 i j
  have key : Ideal.Quotient.mk (Ideal.span {m}) (P i j) = Ideal.Quotient.mk (Ideal.span {m}) ((1 : Matrix n n S) i j) := by
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
    change y * (m : A) = (g : Matrix n n A) i j - _
    rw [e]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Ideal.Quotient.mk (Ideal.span {m}) (P i j) = (1 : Matrix n n _) i j
  rw [key]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end GlobalTheory.CuspNF.KprOpen
