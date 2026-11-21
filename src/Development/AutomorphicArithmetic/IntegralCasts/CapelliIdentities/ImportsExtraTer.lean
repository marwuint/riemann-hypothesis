import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

open Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.Ue16.exists_smul_mem
    {G : Type} [inst : Group G] {LL : Type} [inst_1 : Field LL] {O : Type} [inst_2 : CommRing O]
    [inst_3 : Algebra O LL] [IsDomain O] [IsFractionRing O LL] {V : Type}
    [inst_6 : AddCommGroup V] [inst_7 : Module LL V] [inst_8 : Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (x : V) :
    ∃ a : O, a ≠ 0 ∧ a • x ∈ L.T := by
  have hx : x ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩
