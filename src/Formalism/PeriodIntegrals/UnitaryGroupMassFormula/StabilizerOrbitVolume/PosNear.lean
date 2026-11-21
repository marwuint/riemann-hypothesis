import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

noncomputable section

namespace PI.VolStabSW

namespace PositiveNearLattice

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem crd_map {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (f : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (crd b R y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp [crd]
  | tmul r e =>
    simp [crd, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [crd] at hx hy ⊢
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

theorem crd_incl (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    crd b R (inclR R x) k = algebraMap F R (b.repr x k) := by
  simp [crd, inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) :
    y = ∑ i, crd b R y i • ((1 : R) ⊗ₜ[F] b i) := by
  have := (Algebra.TensorProduct.basis R b).sum_repr y
  simp only [Algebra.TensorProduct.basis_apply] at this
  exact this.symm

variable [FiniteDimensional F E]

theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (k : Fin d) : Continuous (fun y : R ⊗[F] E => crd b R y k) :=
  IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)

include b in
theorem continuous_map_tens {R S : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [Algebra F S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E)) := by
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id F E))) =
      fun y => ∑ k, f (crd b R y k) • ((1 : S) ⊗ₜ[F] b k) := by
    funext y
    rw [eq_sum_crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y)]
    simp only [crd_map]
  rw [e]
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_smul.comp ((hf.comp (continuous_crd b R k)).prodMk continuous_const)

end Coord

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem isClosed_int : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed

theorem isClopen_latV (a M : ℕ) : IsClopen (latV (M := M) (n := a) b v) := by
  have hc : ∀ (x : Fin a) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : latV (M := M) (n := a) b v = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹'
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext Y
    simp [latV, crd]
  rw [e]
  refine ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    (isClosed_int v).preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage (hc x i k)⟩

theorem isCompact_latV (a M : ℕ) : IsCompact (latV (M := M) (n := a) b v) := by
  let L : (Fin a → Fin M → Fin d → Fv F v) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Fv F v) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  let K : Set (Fin a → Fin M → Fin d → Fv F v) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  refine (hK.image hL).of_isClosed_subset (isClopen_latV b v a M).isClosed ?_
  intro Y hY
  refine ⟨fun x i k => crd b (Fv F v) (Y x i) k, ?_, ?_⟩
  · simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro x i k
    exact hY x i k
  · funext x i
    exact (eq_sum_crd b (Fv F v) (Y x i)).symm

end Loc

end PositiveNearLattice

open PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

end PI.VolStabSW
