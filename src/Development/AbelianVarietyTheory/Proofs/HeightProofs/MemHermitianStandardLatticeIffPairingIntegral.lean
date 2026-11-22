import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ShiftMapsUpDown

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.WeilUnramifiedCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_coord (V : HSpace E) (x y : Fin V.rank → E) :
    V.hT (∑ i, x i • V.frame i) (∑ k, y k • V.frame k) = ∑ i, ∑ k, star (x i) * V.gram i k * y k := by
  rw [map_sum V.hT, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, HSpace.gram, starRingEnd_apply]
  ring

theorem mem_hermitianStandardLattice_iff_pairing_integral (V : HSpace E) (x : V.V) : x ∈ V.L0 ↔ ∀ y ∈ V.L0, ∃ o : 𝓞 E, (o : E) = V.hT y x := by
  have h : Formalism.E.hdual V.hT V.L0 = V.L0 := V.baseLattice_isUnimodular
  conv_lhs => rw [← h]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one, LinearMap.restrictScalars_apply]

end Lattice

open GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown (offS homInt homLat latFin latFinAA mapUp mapDown locPart gramFin AEf vacSign vacSignOf theta0
  HyperspecialFixesVacuum HomLatSelfDual mapUp_add mapUp_neg mapUp_zero)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Adeles

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

open Classical in

def idemOff : Af F :=
  ⟨fun v => if v ∈ S then 0 else 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact zero_mem _
    · simp only [h, if_false]; exact one_mem _⟩

variable {F} in
theorem intAf_mul {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

def liftOff : Af F →ₗ[F] AF F :=
  (LinearMap.inr F (Ainf F) (Af F)) ∘ₗ LinearMap.mulLeft F (idemOff F S)

def liftMul {E : Type} [Field E] [Algebra F E] (c : E) : Af F ⊗[F] E →+ AF F ⊗[F] E :=
  ((liftOff F S).rTensor E).toAddMonoidHom.comp (AddMonoidHom.mulLeft ((1 : Af F) ⊗ₜ[F] c))

end Adeles

theorem unramOutside_iff (χ : (AE D)ˣ →* Circle) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Formalism.L2.Theta.UnramOutside D χ S ↔ GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown.UnramOutside D S χ := Iff.rfl

variable {X : ThetaX D} {T : ThetaTied D X}

end GlobalTheory.WeilUnramifiedCompare

end
