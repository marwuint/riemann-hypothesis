import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H.Inh

open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)

theorem relIdx_ne_zero_of_fg {V : Type} [AddCommGroup V] [Module ℂ V] (M M' : AddSubgroup V) [AddGroup.FG M]
    (N : ℕ) (hN : 0 < N) (h : ∀ x ∈ M, N • x ∈ M') : relIdx M' M ≠ 0 := by
  have ht : IsAddTorsion (M ⧸ M'.addSubgroupOf M) := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      refine ⟨N, hN, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact h x x.2
  have := AddCommGroup.finite_of_fg_isAddTorsion _ ht
  exact AddSubgroup.index_ne_zero_of_finite

instance stdLat_fg (L : PeriodPair) (m : Type) [Finite m] : AddGroup.FG (stdLat L m) := by
  rw [← Module.Finite.iff_addGroup_fg]
  have : Module.Finite ℤ L.lattice := ZLattice.module_finite ℝ L.lattice
  let e : (m → L.lattice) ≃+ stdLat L m :=
    { toFun := fun f => ⟨fun i => (f i : ℂ), (mem_stdLat L m _).2 fun i => (f i).2⟩
      invFun := fun x i => ⟨x.1 i, (mem_stdLat L m _).1 x.2 i⟩
      left_inv := fun f => rfl
      right_inv := fun x => rfl
      map_add' := fun f g => rfl }
  exact Module.Finite.equiv e.toIntLinearEquiv

instance imgLat_fg {V : Type} [AddCommGroup V] [Module ℂ V] (g : V →ₗ[ℂ] V) (M : AddSubgroup V) [AddGroup.FG M] :
    AddGroup.FG (imgLat g M) :=
  AddGroup.fg_of_surjective (f := g.toAddMonoidHom.addSubgroupMap M) (g.toAddMonoidHom.addSubgroupMap_surjective M)

abbrev L7 : PeriodPair := cmL 1 1 7 one_pos (by norm_num) 1 one_ne_zero
abbrev th : ℂ := cmTheta 1 7

def uu : ℂ := th ^ 2 / 2

theorem th_rel : th ^ 2 = th - 2 ∧ th + conj th = 1 ∧ th * conj th = 2 := by
  have h := Formalism.L2.Th1.F.cmThetaEq 1 1 2 7 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have := h.1; push_cast at this; rw [this]; ring
  · have := h.2.1; push_cast at this; exact this
  · have := h.2.2; push_cast at this; rw [this]; ring

theorem uu_norm : uu * conj uu = 1 := by
  have h := th_rel.2.2
  simp only [uu, map_div₀, map_pow, map_ofNat]
  have : th ^ 2 / 2 * (conj th ^ 2 / 2) = (th * conj th) ^ 2 / 4 := by ring
  rw [this, h]; norm_num

theorem uu_ne : uu ≠ 0 := fun h => by have := uu_norm; rw [h] at this; simp at this

def smulU (m : Type) : (m → ℂ) ≃ₗ[ℂ] (m → ℂ) := LinearEquiv.smulOfNeZero ℂ _ uu uu_ne

variable (n : Type) [Fintype n] [DecidableEq n]

def gU : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) := smulU (Fin 4 × n)

end Formalism.L2.Th1.H.Inh
