import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.InstTopologicalSpaceHA

noncomputable section

namespace HcS.L2.Fam.SG.Tau

open NumberField IsDedekindDomain HcS.BasicNotions HcS.MainNotions HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix MeasureTheory Filter
open scoped TensorProduct Topology ENNReal NNReal

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Loc

variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def LieU : AddSubgroup (Matrix (Fin M) (Fin M) (R ⊗[F] E)) where
  carrier := {X | HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0}
  zero_mem' := by
    show HcS.UG.cT (sigR R σ) 0 * JR R J + JR R J * 0 = 0
    simp [HcS.UG.cT]
  add_mem' := by
    intro X Y hX hY
    have e : HcS.UG.cT (sigR R σ) (X + Y) = HcS.UG.cT (sigR R σ) X + HcS.UG.cT (sigR R σ) Y := by
      ext i j; simp [HcS.UG.cT]
    show HcS.UG.cT (sigR R σ) (X + Y) * JR R J + JR R J * (X + Y) = 0
    have h1 : HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0 := hX
    have h2 : HcS.UG.cT (sigR R σ) Y * JR R J + JR R J * Y = 0 := hY
    rw [e, add_mul, mul_add, add_add_add_comm, h1, h2, add_zero]
  neg_mem' := by
    intro X hX
    have e : HcS.UG.cT (sigR R σ) (-X) = -HcS.UG.cT (sigR R σ) X := by
      ext i j; simp [HcS.UG.cT]
    show HcS.UG.cT (sigR R σ) (-X) * JR R J + JR R J * (-X) = 0
    have h1 : HcS.UG.cT (sigR R σ) X * JR R J + JR R J * X = 0 := hX
    rw [e, neg_mul, mul_neg, ← neg_add, h1, neg_zero]

instance measLie [TopologicalSpace R] : MeasurableSpace (LieU R σ J) := borel _

def cay (U : Set (LieU R σ J)) : Set (HA R σ J) :=
  {g | ∃ X ∈ U, Units.val (HA.mat R σ J g) * ((1 + 1) - X.1) = (1 + 1) + X.1}

variable {J} {J' : Matrix (Fin M) (Fin M) E} (g : GL (Fin M) (R ⊗[F] E))

variable [TopologicalSpace R] [IsTopologicalRing R]

end Loc

end Defs

end HcS.L2.Fam.SG.Tau

end
