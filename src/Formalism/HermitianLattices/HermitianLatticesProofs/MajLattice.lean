import Mathlib
import Formalism.HermitianLattices.StatementMaj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonMajorizingLattice
import Lemmata.GeneralBFactSecondRest.Imports

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajLatticeAux

variable {K : Type*} [Field K] [NumberField K]

theorem majLattice_common (t : Finset K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ t, IsIntegral ℤ ((d : K) * a) := by
  first | exact UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common .. | (apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› t | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K

end MajLatticeAux

section MajLatticeMain

variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

def majLattice_u (z : ι → mixedSpace K) (v : InfinitePlace K) : ι → ℂ :=
  fun i => (z i).2 ⟨v, IsTotallyComplex.isComplex v⟩

def majLattice_Traw (X : InfinitePlace K → Matrix ι ι ℂ) :
    (ι → mixedSpace K) →ₗ[ℝ] (InfinitePlace K × ι × Fin 2 → ℝ) where
  toFun z p := if p.2.2 = 0 then (((X p.1)⁻¹ *ᵥ majLattice_u z p.1) p.2.1).re
    else (((X p.1)⁻¹ *ᵥ majLattice_u z p.1) p.2.1).im
  map_add' z z' := by
    funext p
    have : majLattice_u (z + z') p.1 = majLattice_u z p.1 + majLattice_u z' p.1 := rfl
    simp only [this, Matrix.mulVec_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' r z := by
    funext p
    have : majLattice_u (r • z) p.1 = r • majLattice_u z p.1 := rfl
    simp only [this, Matrix.mulVec_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def majLattice_alt (X : InfinitePlace K → Matrix ι ι ℂ) :
    (ι → mixedSpace K) →ₗ[ℝ] EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    majLattice_Traw X

theorem majLattice_realize_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    realize b X x = majLattice_alt X (fun i => mixedEmbedding K (b.repr x i)) := by
  rfl

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem majLattice_exists_c (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ L := by
  first | exact Bl.general_b_fact_second_rest.goal1 .. | (apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL y | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V | exact @Bl.general_b_fact_second_rest.goal1 K

theorem majLattice_exists_d (b : Basis ι K V) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((d : K) * b.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd, ht⟩ := majLattice_common (s.biUnion fun g => Finset.univ.image fun i => b.repr g i)
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    exact ht _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro i
    simp only [map_add, Finsupp.add_apply, mul_add]
    exact (hx i).add (hy i)
  | smul r x _ hx =>
    intro i
    have : b.repr (r • x) i = algebraMap (𝓞 K) K r * b.repr x i := by
      rw [← algebraMap_smul K r x, map_smul]; rfl
    rw [this, mul_left_comm]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx i)

theorem majLattice_mem_zmap (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    w ∈ zmap (realize b X) L ↔ ∃ x ∈ L, realize b X x = w := Iff.rfl

end MajLatticeMain

end Formalism.HermitianLatticesTheory
