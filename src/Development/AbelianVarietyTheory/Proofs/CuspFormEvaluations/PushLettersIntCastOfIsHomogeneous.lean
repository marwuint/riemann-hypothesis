import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo

open MvPolynomial Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.Harm

section Free

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ ι : Type*}

noncomputable def basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (b.repr (coeff m P) i)

theorem coeff_basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S)
    (m : σ →₀ ℕ) : coeff m (basisComponent b i P) = b.repr (coeff m P) i := by
  classical
  rw [basisComponent, coeff_sum, Finset.sum_eq_single m]
  · simp
  · intro m' _ h; simp [coeff_monomial, h]
  · intro h; simp [notMem_support_iff.1 h]

theorem exists_eq_sum_basisComponent (b : Module.Basis ι R S) (P : MvPolynomial σ S) :
    ∃ J : Finset ι, P = ∑ i ∈ J, b i • MvPolynomial.map (algebraMap R S) (basisComponent b i P) := by
  classical
  refine ⟨P.support.biUnion fun m => (b.repr (coeff m P)).support, ?_⟩
  ext m
  simp only [coeff_sum, coeff_smul, coeff_map, coeff_basisComponent, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (coeff m P), Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset (s := P.support.biUnion fun m => (b.repr (coeff m P)).support)]
  · exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
  · by_cases hm : m ∈ P.support
    · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (coeff m P)).support) hm
    · simp [notMem_support_iff.1 hm]
  · simp

theorem basisComponent_sum (b : Module.Basis ι R S) (J : Finset ι) (Q : ι → MvPolynomial σ R)
    {i : ι} (hi : i ∈ J) :
    basisComponent b i (∑ j ∈ J, b j • MvPolynomial.map (algebraMap R S) (Q j)) = Q i := by
  classical
  ext m
  simp only [coeff_basisComponent, coeff_sum, coeff_smul, coeff_map, smul_eq_mul, mul_comm (b _),
    ← Algebra.smul_def, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single i] <;> simp +contextual [hi]

variable {T : Type*} {p q : ℕ} {κ : Type*} [Fintype κ] {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}

theorem basisComponent_mem_rowHighest (b : Module.Basis ι R S) (i : ι) {P : Poly S T p q κ}
    (hP : P ∈ rowHighest S c c') : basisComponent b i P ∈ rowHighest R c c' := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
  by_cases hi : i ∈ J
  swap
  · have : basisComponent b i P = 0 := by
      rw [← basisComponent_sum b (insert i J)
        (fun j => if j = i then 0 else basisComponent b j P) (Finset.mem_insert_self i J)
        |>.trans (if_pos rfl)]
      congr 1
      rw [Finset.sum_insert hi, if_pos rfl, map_zero, smul_zero, zero_add]
      refine hJ.trans (Finset.sum_congr rfl fun j hj => ?_)
      rw [if_neg (by rintro rfl; exact hi hj)]
    rw [this]; exact zero_mem _
  refine mem_rowHighest_iff_rowAdd.2 ⟨fun t a b' => ?_, fun t r m hm => h₂ t r fun e => hm ?_,
    fun t r r' hr s => ?_⟩
  · have := h₁ t a b'
    rw [hJ, map_sum] at this
    simp only [map_smul, ← map_laplacian] at this
    rw [← basisComponent_sum b J (fun j => laplacian t a b' (basisComponent b j P)) hi, this]
    simp [basisComponent]
  · rw [coeff_basisComponent, e]; simp
  · have := h₃ t r r' hr s
    conv_lhs at this => rw [hJ, map_sum]
    simp only [map_smul, ← map_intCast (algebraMap R S), ← map_rowAdd] at this
    rw [← basisComponent_sum b J (fun j => rowAdd t r r' (s : R) (basisComponent b j P)) hi, this]

variable (R S c c') in

theorem span_map_rowHighest [Module.Free R S] :
    Submodule.span S (MvPolynomial.map (algebraMap R S) ''
      (rowHighest R (κ := κ) c c' : Set (Poly R T p q κ))) = rowHighest S c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    exact map_mem_rowHighest _ hP
  · intro P hP
    let b := Module.Free.chooseBasis R S
    obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
    rw [hJ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, basisComponent_mem_rowHighest b i hP, rfl⟩)

end Free

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type*} [Field K]
  {T : Type*} {p q n : ℕ}

noncomputable abbrev ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E ≃ₐ[_] E)

theorem herm_one_eq_sum (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]

variable (p q) in

noncomputable def symO (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Subalgebra (𝓞 K) (Poly K T p q (Fin n)) :=
  Algebra.adjoin (𝓞 K)
    ({P | ∃ t a, ∃ v ∈ Λ, P = xForm t a fun k => τ t (v k)} ∪
      {P | ∃ t b, ∃ v ∈ Λ, P = yForm t b fun k => τ t (cc (v k))})

noncomputable def Ha (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (Poly K T p q (Fin n)) :=
  (rowHighest K c c').restrictScalars (𝓞 K) ⊓ Subalgebra.toSubmodule (symO p q τ Λ)

variable (τ : T → E →+* K) {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
  {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {P : Poly K T p q (Fin n)}

variable [NumberField K]

variable [Fintype T]

end Lattice

end GlobalTheory.Harm
