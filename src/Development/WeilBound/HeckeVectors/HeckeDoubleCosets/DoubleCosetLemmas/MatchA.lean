import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

theorem absV_mul (x y : Cv v) : absV v (x * y) = absV v x * absV v y := by simp [absV]

theorem absV_nonneg (x : Cv v) : 0 ≤ absV v x := NNReal.coe_nonneg _

theorem absV_one : absV v (1 : Cv v) = 1 := by simp [absV]

def wt (s : ℝ) {m : ℕ} (g : GL (Fin m) (Cv v)) : ℂ := ((absV v g.1.det ^ s : ℝ) : ℂ)

theorem wt_one (s : ℝ) {m : ℕ} : wt s (1 : GL (Fin m) (Cv v)) = 1 := by simp [wt, absV_one]

theorem wt_mul (s : ℝ) {m : ℕ} (g h : GL (Fin m) (Cv v)) : wt s (g * h) = wt s g * wt s h := by
  simp only [wt, Units.val_mul, det_mul, absV_mul, Real.mul_rpow (absV_nonneg _) (absV_nonneg _),
    Complex.ofReal_mul]

def rep {X : Type} {m : ℕ} (s : ℝ) (a : X → GL (Fin m) (Cv v) → X) (a1 : ∀ y, a y 1 = y)
    (am : ∀ y g h, a y (g * h) = a (a y g) h) : Representation ℂ (GL (Fin m) (Cv v)) (X → ℂ) where
  toFun g :=
    { toFun := fun Φ y => wt s g * Φ (a y g)
      map_add' := fun Φ Ψ => funext fun y => by simp [mul_add]
      map_smul' := fun c Φ => funext fun y => by simp [mul_left_comm] }
  map_one' := by ext Φ y; simp [wt_one, a1]
  map_mul' g h := by ext Φ y; simp [wt_mul, am, mul_assoc]

variable (v) in

def rS (n c : ℕ) : Representation ℂ (GL (Fin c) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) :=
  rep ((n : ℝ) / 2) (fun y g => y * g.1) (by simp) (by simp [Matrix.mul_assoc])

variable (v) in

def rT (n c : ℕ) : Representation ℂ (GL (Fin n) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) :=
  rep ((c : ℝ) / 2) (fun y z => z.1ᵀ * y) (by simp)
    (by simp [Matrix.mul_assoc, Matrix.transpose_mul])

theorem rS_apply {n c : ℕ} (g : GL (Fin c) (Cv v)) (Φ) (y) :
    rS v n c g Φ y = wt ((n : ℝ) / 2) g * Φ (y * g.1) := rfl

theorem rT_apply {n c : ℕ} (z : GL (Fin n) (Cv v)) (Φ) (y) :
    rT v n c z Φ y = wt ((c : ℝ) / 2) z * Φ (z.1ᵀ * y) := rfl

end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
