import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

private lemma exists_ne_zero_smul_mem_of_span_eq_top_alt {O LL V : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (h : Submodule.span LL (T : Set V) = ⊤) (v : V) :
    ∃ a : O, a ≠ 0 ∧ a • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact T.smul_mem _ hax
    · rw [mul_smul]; exact T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hd : (d : O) ≠ 0 := nonZeroDivisors.ne_zero d.2
    refine ⟨(d : O) * a, mul_ne_zero hd ha, ?_⟩
    have key : ((d : O) * a) • c • x = n • a • x := by
      have e : ∀ (r : O) (y : V), r • y = (algebraMap O LL r) • y :=
        fun r y => (algebraMap_smul LL r y).symm
      have hnd' : c * algebraMap O LL (d : O) = algebraMap O LL n := hnd
      rw [e ((d : O) * a), e n, e a, smul_smul, smul_smul, map_mul, ← hnd']
      congr 1
      ring
    rw [key]
    exact T.smul_mem _ hax

open Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem
    {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    {Qp LL O : Type} [inst_2 : Field Qp] [inst_3 : Field LL] [inst_4 : Algebra Qp LL]
    [inst_5 : CommRing O] [inst_6 : Algebra O LL] [inst_7 : TopologicalSpace LL]
    (A : GRep G Qp LL O) (LA : @Lattice G inst LL inst_3 O inst_5 A.V A.acg A.modLL A.modO A.ρ)
    [IsDomain O] [IsFractionRing O LL] (v : A.V) :
    letI := A.acg
    letI := A.modO
    ∃ a : O, a ≠ 0 ∧ a • v ∈ LA.T := by
  let _ := A.acg
  let _ := A.modLL
  let _ := A.modO
  have _ := A.towO
  obtain ⟨T, _, _, _, hs⟩ := LA
  exact exists_ne_zero_smul_mem_of_span_eq_top_alt T hs v
