import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Cochains

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]

theorem cochainOf_cochainsMap_f (f : A ⟶ B) {i : ℕ} (a : (cochainsComplex A).X i) :
    cochainOf B ((cochainsMap f).f i a) = fun σ => f.hom (cochainOf A a σ) :=
  rfl

end Cochains

section Connecting

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃]

theorem δ_cohomologyπ_of_lift (hS : S.ShortExact) {i j : ℕ} (hij : i + 1 = j)
    (x₃ : cocycles S.X₃ i) (x₂ : (cochainsComplex S.X₂).X i)
    (hx₂ : (cochainsMap S.g).f i x₂ = cocycleι S.X₃ i x₃) (x₁ : cocycles S.X₁ j)
    (hx₁ : (cochainsMap S.f).f j (cocycleι S.X₁ j x₁) =
      (cochainsComplex S.X₂).d i j x₂) :
    δ hS i j hij (cohomologyπ S.X₃ i x₃) = cohomologyπ S.X₁ j x₁ := by
  have hx₃ : (cochainsComplex S.X₃).d i j (cocycleι S.X₃ i x₃) = 0 :=
    ConcreteCategory.congr_hom ((cochainsComplex S.X₃).iCycles_d i j) x₃
  have key := (cochainsShortComplex_shortExact hS).δ_apply i j hij (cocycleι S.X₃ i x₃) hx₃ x₂
    hx₂ (cocycleι S.X₁ j x₁) hx₁ (j + 1) (by simp)
  have e3 : (cochainsComplex S.X₃).cyclesMk (cocycleι S.X₃ i x₃) j
      ((ComplexShape.up ℕ).next_eq' hij) hx₃ = x₃ :=
    cocycleι_injective ((cochainsComplex S.X₃).i_cyclesMk _ _ _ _)
  have e1 : (cochainsComplex S.X₁).cyclesMk (cocycleι S.X₁ j x₁) (j + 1) (by simp)
      ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂
        (cocycleι S.X₁ j x₁) hx₁ (j + 1)) = x₁ :=
    cocycleι_injective ((cochainsComplex S.X₁).i_cyclesMk _ _ _ _)
  calc δ hS i j hij (cohomologyπ S.X₃ i x₃)
      = δ hS i j hij (cohomologyπ S.X₃ i ((cochainsComplex S.X₃).cyclesMk (cocycleι S.X₃ i x₃) j
          ((ComplexShape.up ℕ).next_eq' hij) hx₃)) := by rw [e3]
    _ = cohomologyπ S.X₁ j ((cochainsComplex S.X₁).cyclesMk (cocycleι S.X₁ j x₁) (j + 1)
          (by simp) ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂
            (cocycleι S.X₁ j x₁) hx₁ (j + 1))) := key
    _ = cohomologyπ S.X₁ j x₁ := by rw [e1]

theorem exists_cocycle_map_f_eq_d (hS : S.ShortExact) {i : ℕ} (j : ℕ)
    (x₃ : cocycles S.X₃ i) (x₂ : (cochainsComplex S.X₂).X i)
    (hx₂ : (cochainsMap S.g).f i x₂ = cocycleι S.X₃ i x₃) :
    ∃ x₁ : cocycles S.X₁ j, (cochainsMap S.f).f j (cocycleι S.X₁ j x₁) =
      (cochainsComplex S.X₂).d i j x₂ := by
  have hex := (HomologicalComplex.exact_iff_degreewise_exact _).1
    (cochainsShortComplex_shortExact hS).exact j
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hz : ((cochainsMap S.g).f j).hom ((cochainsComplex S.X₂).d i j x₂) = 0 := by
    have hc := ConcreteCategory.congr_hom ((cochainsMap S.g).comm i j) x₂
    have hd := ConcreteCategory.congr_hom ((cochainsComplex S.X₃).iCycles_d i j) x₃
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hc
    rw [ConcreteCategory.comp_apply] at hd
    rw [← hc, hx₂]
    exact hd
  obtain ⟨x₁, hx₁⟩ := hex _ hz
  have hx₁' : (cochainsMap S.f).f j x₁ = (cochainsComplex S.X₂).d i j x₂ := hx₁
  refine ⟨(cochainsComplex S.X₁).cyclesMk x₁ (j + 1) (by simp)
    ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂ x₁ hx₁' (j + 1)), ?_⟩
  have e : cocycleι S.X₁ j ((cochainsComplex S.X₁).cyclesMk x₁ (j + 1) (by simp)
      ((cochainsShortComplex_shortExact hS).d_eq_zero_of_f_eq_d_apply i j x₂ x₁ hx₁'
        (j + 1))) = x₁ :=
    (cochainsComplex S.X₁).i_cyclesMk _ _ _ _
  rw [e]
  exact hx₁'

end Connecting

section TensorRight

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] (B : Rep.{u} k G) [IsDiscreteRep B]

instance isDiscreteRep_map_tensorRight_X₁ : IsDiscreteRep (S.map (tensorRight B)).X₁ :=
  isDiscreteRep_tensor S.X₁ B

instance isDiscreteRep_map_tensorRight_X₂ : IsDiscreteRep (S.map (tensorRight B)).X₂ :=
  isDiscreteRep_tensor S.X₂ B

instance isDiscreteRep_map_tensorRight_X₃ : IsDiscreteRep (S.map (tensorRight B)).X₃ :=
  isDiscreteRep_tensor S.X₃ B

variable {B}

end TensorRight

section TensorLeft

variable {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] (B : Rep.{u} k G) [IsDiscreteRep B]

instance isDiscreteRep_map_tensorLeft_X₁ : IsDiscreteRep (S.map (tensorLeft B)).X₁ :=
  isDiscreteRep_tensor B S.X₁

instance isDiscreteRep_map_tensorLeft_X₂ : IsDiscreteRep (S.map (tensorLeft B)).X₂ :=
  isDiscreteRep_tensor B S.X₂

instance isDiscreteRep_map_tensorLeft_X₃ : IsDiscreteRep (S.map (tensorLeft B)).X₃ :=
  isDiscreteRep_tensor B S.X₃

variable {B}

end TensorLeft

end GroundTheory.ProfCoh
