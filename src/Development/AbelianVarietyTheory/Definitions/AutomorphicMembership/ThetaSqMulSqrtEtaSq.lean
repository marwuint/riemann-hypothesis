import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ChiGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorial
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamHomogOfHomog
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaPowAndDegree
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaOfConnFam
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDatumConnectedFamilyOfPolarizedArithmeticFami
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarizedFamilyOfThetaUniformization

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyPow GlobalTheory.KeyCl

noncomputable section
namespace GlobalTheory.LocM

structure NgC (g : ℕ) : Type where

  τ : Matrix (Fin g) (Fin g) ℂ
  symm : τ.IsSymm
  pos : (τ.map Complex.im).PosDef

  a : Fin g → ℂ

  b : Fin g → ℂ
  half : charHalf g a b

namespace NgC

variable {g : ℕ}

def base (g : ℕ) (a b : Fin g → ℂ) (h : charHalf g a b) : NgC g :=
  ⟨_, (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).1,
    (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).2, a, b, h⟩

instance (g : ℕ) : Nonempty (NgC g) := ⟨base g 0 0 ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩⟩

def Y (z : NgC g) : Matrix (Fin g) (Fin g) ℝ := z.τ.map Complex.im

def Frame (z : NgC g) (x : KeyIn ℂ) : Prop :=
  ∃ h : x.P.g = g, NormalAt x (z.τ.submatrix (Fin.cast h) (Fin.cast h)) 1
    (fun i => z.a (i.cast h)) (fun i => z.b (i.cast h)) 1

def Lies (z : NgC g) (x : KeyIn ℂ) : Prop := KeyEq.Nrm x z.τ z.a z.b

theorem Frame.lies {z : NgC g} {x : KeyIn ℂ} (h : z.Frame x) : z.Lies x := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, 1, 1, one_ne_zero, h⟩

def cubSq (z : NgC g) (w : Fin g → ℂ) : ℝ :=
  ‖thetaChar z.τ z.a z.b w‖ ^ 2 *
    Real.exp (-2 * Real.pi * ((fun i => (w i).im) ⬝ᵥ (z.Y)⁻¹.mulVec fun i => (w i).im))

def thetaSq (z : NgC g) : ℝ :=
  ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
    z.cubSq ((fun i => (p (.inl i) : ℂ)) + z.τ.mulVec (fun i => (p (.inr i) : ℂ)))

def lieGram (z : NgC g) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => Real.pi * hermForm ((z.Y)⁻¹.map fun x : ℝ => (x : ℂ))
    (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (Pi.single j (2 * Real.pi * Complex.I)⁻¹)

def etaSq (z : NgC g) : ℝ := (z.lieGram.det.re)⁻¹

end NgC

structure IsKF (g c : ℕ) (κ : Rule) : Prop where
  homog : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
    (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
    (∀ i, IsLieComb (M i) v (v' i)) →
    a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩
  funct : Funct κ
  unitSp : UnitSp κ
  off : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), x.P.g ≠ g → κ K x = 1

structure KF (g c : ℕ) : Type where

  val : NgC g → ℂˣ
  ex : ∃ κ : Rule, IsKF g c κ ∧ ∀ (z : NgC g) (x : KeyIn ℂ), z.Frame x → κ ℂ x = (val z)⁻¹
  zero : g = 0 → ∀ z, val z = 1 ∨ val z = -1

namespace KF

variable {g c : ℕ} (kf : KF g c)

def rule : Rule := kf.ex.choose

@[ext] theorem ext {kf kf' : KF g c} (h : kf.val = kf'.val) : kf = kf' := by
  cases kf; cases kf'; cases h; rfl

def coef (K : Type) [Field K] [CharZero K] (x : KeyIn K) : Kˣ := (kf.rule K x)⁻¹

def norm (z : NgC g) : ℝ := ‖(kf.val z : ℂ)‖ / (z.thetaSq ^ c * Real.sqrt z.etaSq ^ c)

end KF

def ngTrue : Formalism.L2.Geo.NgPkg where
  NgC := NgC
  NgC_ne _ := inferInstance
  KF := KF
  kfNorm kf z := kf.norm z

end GlobalTheory.LocM
end
