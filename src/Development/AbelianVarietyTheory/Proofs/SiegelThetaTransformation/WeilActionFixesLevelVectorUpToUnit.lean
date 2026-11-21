import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransportStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinitePointsCarryLatticeVacuumToMovedVacuum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LevEig

section Hat

variable {D : D7} {k : ℕ}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem tmul_mem_hatV {L : Lt D.host.E k} {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : Fin k → D.host.E}
    (hx : x ∈ L) : (fun i => a ⊗ₜ[D.host.F] x i) ∈ hatV L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem toAf_mem {L : Lt D.host.E k} {x : Fin k → D.host.E} (hx : x ∈ L) : toAf x ∈ hatV L :=
  tmul_mem_hatV one_mem_intAf hx

theorem toAf_sub (x y : Fin k → D.host.E) : toAf (x - y) = toAf x - toAf y := by
  funext i; exact TensorProduct.tmul_sub _ _ _

theorem hatV_map {G : Type} [AddCommGroup G] {L : Lt D.host.E k} (f : (Fin k → AfE D) →+ G) (H : AddSubgroup G)
    (h : ∀ a ∈ intAf D.host.F, ∀ x ∈ L, f (fun i => a ⊗ₜ[D.host.F] x i) ∈ H) {u} (hu : u ∈ hatV L) : f u ∈ H := by
  refine (AddSubgroup.closure_le (H.comap f)).2 ?_ hu
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact h a ha x hx

theorem smul_mem_hatV {L L' : Lt D.host.E k} (c : 𝓞 D.host.E) (h : ∀ x ∈ L, c • x ∈ L') {u} (hu : u ∈ hatV L) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • u ∈ hatV L' := by
  refine hatV_map (DistribSMul.toAddMonoidHom _ ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E))) _
    (fun a ha x hx => ?_) hu
  convert tmul_mem_hatV ha (h x hx) using 1
  funext i
  simp only [DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem nsmul_mem_hatV {L : Lt D.host.E k} {𝔪 : Ideal (𝓞 D.host.E)} {M : ℕ} (hM : (M : 𝓞 D.host.E) ∈ 𝔪) {u}
    (hu : u ∈ hatV L) : M • u ∈ hatV (𝔪 • L) := by
  have := smul_mem_hatV (L' := 𝔪 • L) M (fun x hx => Submodule.smul_mem_smul hM hx) hu
  have e : ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : 𝓞 D.host.E) : D.host.E)) = (M : AfE D) :=
    map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)).toRingHom.comp
      (algebraMap (𝓞 D.host.E) D.host.E)) M
  rwa [e, Nat.cast_smul_eq_nsmul] at this

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

variable {S T : HSp D}

theorem actO_sub (h : GA D S) (g : GA D T) (w w' : WO S T) :
    actO S T h g (w - w') = actO S T h g w - actO S T h g w' := by
  simp only [actO, Matrix.mul_sub, Matrix.sub_mul]

end Hat

end GlobalTheory.Ker.LevEig
