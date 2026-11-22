import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipCT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem isClosed_line {d : ℕ} (x : Fin d → E) :
    IsClosed (Set.range fun a : AE F E => a • incV F x) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  by_cases hx : x = 0
  · subst hx
    have h0 : incV F (0 : Fin d → E) = 0 := by ext i; simp [incV]
    have : (Set.range fun a : AE F E => a • incV F (0 : Fin d → E)) = {0} := by
      ext v; simp [h0, eq_comm]
    rw [this]; exact isClosed_singleton
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    set c : AE F E := inclR (F := F) (AF F) (x i)⁻¹
    have hxc : inclR (F := F) (AF F) (x i) * c = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hi, map_one]
    have : (Set.range fun a : AE F E => a • incV F x) = {v | v = (v i * c) • incV F x} := by
      ext v
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, incV]
        rw [mul_assoc, hxc, mul_one]
      · intro h; exact ⟨_, h.symm⟩
    rw [this]
    exact isClosed_eq continuous_id (((continuous_apply i).mul continuous_const).smul continuous_const)

variable (σ) in

def unipSet {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}
  one_mem' := by
    refine ⟨by simp [mat], fun z => ⟨0, by simp [mat]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul', ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul', ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, hu1, ha, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have h1 : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    refine ⟨h1, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h2 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, h1] at h2
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]; exact h2

theorem unip_eq {d d₁ : ℕ} (σ : E →ₐ[F] E) (W : Spc F E d) (H' : Plane E d d₁) : unip σ W H' = unipSet σ W H' :=
  le_antisymm ((Subgroup.closure_le _).2 fun _ h => h) fun _ h => Subgroup.subset_closure h

theorem isClosed_unip {d d₁ : ℕ} (σ : E →ₐ[F] E) (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  rw [unip_eq]
  have hS : ((unipSet σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) = {u | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z, {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]; rfl
  rw [hS]
  refine (isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const).inter (isClosed_iInter fun z => ?_)
  have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
      (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹' Set.range fun a : AE F E => a • incV F H'.x := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
    exact exists_congr fun a => by rw [eq_sub_iff_add_eq', eq_comm]
  rw [this]
  exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)

theorem countable_ratU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun g : GL (Fin n) E => (g.1, g.inv)) fun g h hgh => Units.ext (congrArg Prod.fst hgh)
  have hr : Set.Countable (((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :
      Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) := by
    rw [MonoidHom.coe_range]; exact Set.countable_range _
  haveI := hr.to_subtype
  exact Function.Injective.countable (f := fun g : ratU σ J => (⟨g.1.1, g.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range))
    fun g h hgh => by
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hgh

end GlobalTheory.UnipCT

end
