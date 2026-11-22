import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary

noncomputable section

namespace GlobalTheory.ThK.ConeEuler.UnitsOpen

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_integral_everywhere : IsOpen {z : AE F E | ∀ v : Pl F, compFin F E v z ∈ intLoc F E v} := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let S : AddSubgroup (AE F E) :=
    { carrier := {z | ∀ v : Pl F, compFin F E v z ∈ intLoc F E v}
      zero_mem' := fun v => by rw [map_zero]; exact zero_mem _
      add_mem' := fun ha hb v => by rw [map_add]; exact add_mem (ha v) (hb v)
      neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v) }
  let b := integralBasis E
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → AF F) →ₗ[AF F] AE F E :=
    Fintype.linearCombination (AF F) fun i => (1 : AF F) ⊗ₜ[F] b i
  have hφ : ∀ a, φ a = ∑ i, a i ⊗ₜ[F] b i := fun a => by
    simp only [φ, Fintype.linearCombination_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hq : ∀ (c : ℚ) (a : AF F) (x : E), a ⊗ₜ[F] (c • x) = (algebraMap F (AF F) (c : F) * a) ⊗ₜ[F] x := fun c a x => by
    rw [show c • x = (c : F) • x by rw [Rat.cast_smul_eq_qsmul], ← TensorProduct.smul_tmul, Algebra.smul_def]
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a x =>
      refine ⟨fun i => algebraMap F (AF F) (b.repr x i : F) * a, ?_⟩
      rw [hφ]
      conv_rhs => rw [← b.sum_repr x, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ => (hq _ _ _).symm
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hy
      exact ⟨a + c, map_add _ _ _⟩
  let W : Set (AF F) := {a | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  have ho : IsOpen W :=
    (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) =>
      Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd
  have hopen : IsOpen (φ '' Set.univ.pi fun _ => W) :=
    (IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap _
      (isOpen_set_pi Set.finite_univ fun _ _ => ho)
  have hsub : φ '' (Set.univ.pi fun _ => W) ⊆ (S : Set (AE F E)) := by
    rintro _ ⟨a, ha, rfl⟩ v
    rw [hφ, map_sum]
    refine sum_mem fun i _ => ?_
    rw [show b i = ((RingOfIntegers.basis E i : 𝓞 E) : E) from integralBasis_apply E i]
    exact tmul_mem_intLoc (ha i (Set.mem_univ i) v) _
  have h0 : (0 : AE F E) ∈ φ '' (Set.univ.pi fun _ => W) :=
    ⟨0, fun i _ v => by simp, map_zero φ⟩
  exact (AddSubgroup.isOpen_of_mem_nhds S (g := 0) (Filter.mem_of_superset (hopen.mem_nhds h0) hsub) :
    IsOpen (S : Set (AE F E)))

end Lemmas

end GlobalTheory.ThK.ConeEuler.UnitsOpen

namespace GlobalTheory.ThK.ConeEuler

end GlobalTheory.ThK.ConeEuler
