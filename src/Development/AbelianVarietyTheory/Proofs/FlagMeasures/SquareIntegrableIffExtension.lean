import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.SqIntSU

variable {n : ℕ}

def circleBorelMS : MeasurableSpace Circle := borel Circle

attribute [local instance] circleBorelMS

theorem circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

attribute [local instance] circleBorelSpace

theorem circle_star_mul (z : Circle) : star (z : ℂ) * z = 1 := by
  rw [Complex.star_def, Complex.conj_mul', Circle.norm_coe]
  norm_num

theorem circle_mul_star (z : Circle) : (z : ℂ) * star (z : ℂ) = 1 := by
  rw [mul_comm]
  exact circle_star_mul z

section Scal

variable (ε : Fin n → Bool)

def unitScalar (z : Circle) : UJ ε :=
  ⟨⟨(z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ), star (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ),
    by rw [smul_mul_smul_comm, circle_mul_star, Matrix.one_mul, one_smul],
    by rw [smul_mul_smul_comm, circle_star_mul, Matrix.one_mul, one_smul]⟩, by
    show ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * Jm ε * ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = Jm ε
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, circle_star_mul, circle_mul_star, one_smul]⟩

theorem umat_unitScalar (z : Circle) : umat (unitScalar ε z) = (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := rfl

theorem unitScalar_comm (z : Circle) (g : UJ ε) : unitScalar ε z * g = g * unitScalar ε z := by
  apply Subtype.ext
  apply Units.ext
  show umat (unitScalar ε z) * umat g = umat g * umat (unitScalar ε z)
  rw [umat_unitScalar, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

theorem unitScalar_mul (a b : Circle) : unitScalar ε (a * b) = unitScalar ε a * unitScalar ε b := by
  apply Subtype.ext
  apply Units.ext
  show ((a * b : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
    ((a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
  rw [Circle.coe_mul, smul_mul_smul_comm, Matrix.one_mul]

theorem unitScalar_one : unitScalar ε 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show ((1 : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Circle.coe_one, one_smul]

theorem isClosed_special : IsClosed (SUJ ε : Set (UJ ε)) :=
  isClosed_eq (Units.continuous_val.comp continuous_subtype_val).matrix_det continuous_const

theorem locallyCompact_special : LocallyCompactSpace (SUJ ε) :=
  (isClosed_special ε).isClosedEmbedding_subtypeVal.locallyCompactSpace

attribute [local instance] locallyCompact_special

theorem secondCountable_special : SecondCountableTopology (SUJ ε) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

attribute [local instance] secondCountable_special

theorem sigmaCompact_special : SigmaCompactSpace (SUJ ε) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

attribute [local instance] sigmaCompact_special

def scalarMul : Circle × SUJ ε →* UJ ε where
  toFun p := unitScalar ε p.1 * (p.2 : UJ ε)
  map_one' := by
    show unitScalar ε 1 * 1 = 1
    rw [unitScalar_one, one_mul]
  map_mul' := by
    rintro ⟨a, g⟩ ⟨b, h⟩
    show unitScalar ε (a * b) * ((g * h : SUJ ε) : UJ ε) = unitScalar ε a * (g : UJ ε) * (unitScalar ε b * (h : UJ ε))
    calc unitScalar ε (a * b) * ((g * h : SUJ ε) : UJ ε) = unitScalar ε a * (unitScalar ε b * (g : UJ ε)) * (h : UJ ε) := by
          rw [Subgroup.coe_mul, unitScalar_mul]
          simp only [mul_assoc]
      _ = unitScalar ε a * ((g : UJ ε) * unitScalar ε b) * (h : UJ ε) := by rw [unitScalar_comm ε b (g : UJ ε)]
      _ = unitScalar ε a * (g : UJ ε) * (unitScalar ε b * (h : UJ ε)) := by simp only [mul_assoc]

theorem scalarMul_apply (z : Circle) (g : SUJ ε) : scalarMul ε (z, g) = unitScalar ε z * (g : UJ ε) := rfl

def circleHaar : Measure Circle := Measure.haarMeasure ⊤

theorem circleHaar_isHaar : circleHaar.IsHaarMeasure := by
  unfold circleHaar
  infer_instance

attribute [local instance] circleHaar_isHaar

theorem circleHaar_finite : IsFiniteMeasure circleHaar := CompactSpace.isFiniteMeasure

attribute [local instance] circleHaar_finite

end Scal

end GlobalTheory.SqIntSU

noncomputable section

namespace GlobalTheory.SqIntSU

end GlobalTheory.SqIntSU
