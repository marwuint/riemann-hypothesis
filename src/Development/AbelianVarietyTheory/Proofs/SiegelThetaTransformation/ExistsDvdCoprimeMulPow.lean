import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.DCos

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ}

theorem tmul_mem {L : Set (Fin k → E)} {a : Af F} (ha : a ∈ intAf F)
    {x : Fin k → E} (hx : x ∈ L) : (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem map_mem_latHat {L L' : Set (Fin k → E)} (f : (Fin k → Af F ⊗[F] E) →+ (Fin k → Af F ⊗[F] E))
    (h : ∀ a ∈ intAf F, ∀ x ∈ L, f (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L') {u : Fin k → Af F ⊗[F] E}
    (hu : u ∈ latHat F E L) : f u ∈ latHat F E L' := by
  have : latHat F E L ≤ (latHat F E L').comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact h a ha x hx
  exact this hu

theorem mulVec_mem_latHat {L L' : Set (Fin k → E)} {δ : Matrix (Fin k) (Fin k) E}
    (h : ∀ v ∈ L, δ *ᵥ v ∈ L') {u : Fin k → Af F ⊗[F] E} (hu : u ∈ latHat F E L) :
    δ.map (inclR (F := F) (Af F)) *ᵥ u ∈ latHat F E L' := by
  refine map_mem_latHat (Matrix.mulVecLin (δ.map (inclR (F := F) (Af F)))).toAddMonoidHom
    (fun b hb x hx => ?_) hu
  convert tmul_mem hb (h x hx) using 1
  funext i
  change ∑ j, ((1 : Af F) ⊗ₜ[F] δ i j : Af F ⊗[F] E) * b ⊗ₜ[F] x j = b ⊗ₜ[F] ∑ j, δ i j * x j
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Adelic

end GlobalTheory.Ker.DCos

end
