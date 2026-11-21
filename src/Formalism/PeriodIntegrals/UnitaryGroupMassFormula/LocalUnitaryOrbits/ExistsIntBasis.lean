import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.ContinuousHRRight

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def oevS : AddSubgroup (Fv F v ⊗[F] E) :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).toAddSubgroup

theorem coe_oevS : (oevS (E := E) v : Set (Fv F v ⊗[F] E)) = OEv (E := E) v := rfl

theorem inclR_mem_oev (x : 𝓞 E) : inclR (F := F) (Fv F v) (x : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩

theorem exists_int_basis : ∃ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ k, IsIntegral ℤ (b k) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (Module.finBasis F E))
  have hyF : IsUnit ((y : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hy
  refine ⟨_, (Module.finBasis F E).isUnitSMul (fun _ => hyF), fun k => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
  exact hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

theorem latA_le_oevS [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (hb : ∀ k, IsIntegral ℤ (b k)) : latA v b ≤ oevS (E := E) v := by
  intro z hz
  have hz' : ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F := hz
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]
  have hm : inclR (F := F) (Fv F v) (((⟨b k, hb k⟩ : 𝓞 E)) : E) ∈ OEv (E := E) v :=
    inclR_mem_oev v (⟨b k, hb k⟩ : 𝓞 E)
  exact Submodule.smul_mem _ (⟨_, hz' k⟩ : v.adicCompletionIntegers F) hm

theorem isOpen_oev : IsOpen (OEv (E := E) v) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  rw [← coe_oevS]
  exact AddSubgroup.isOpen_mono (latA_le_oevS v b hb) (isOpen_latA v b)

theorem isCompact_oev : IsCompact (OEv (E := E) v) :=
  LocMassOrdKv.isCompact_oev v

variable (σ : E →ₐ[F] E)

theorem coe_HO (a : ℕ) : (HO σ v a : Set (HermR (Fv F v) σ a)) =
    Subtype.val ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) := by
  ext S
  constructor
  · intro h
    rw [SetLike.mem_coe, mem_HO] at h
    exact fun i _ j _ => h i j
  · intro h
    rw [SetLike.mem_coe, mem_HO]
    exact fun i j => h i (Set.mem_univ _) j (Set.mem_univ _)

theorem topH_holds (a : ℕ) : TopH σ v a := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oev v
  have := locallyCompact_Fv F v
  refine ⟨?_, ?_⟩
  · rw [coe_HO]
    exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  · rw [coe_HO]
    exact (isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v).preimage continuous_subtype_val

end Top

end PI.OmLocU
