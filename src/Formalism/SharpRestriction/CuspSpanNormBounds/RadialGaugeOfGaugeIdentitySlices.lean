import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Formalism.HermitianCurvature.StatementWd
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialLemmaE
import Formalism.SharpRestriction.CuspSpanNormBounds.ChoiceOfModulusAndDiscriminant
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialRules
import Formalism.SharpRestriction.CuspSpanNormBounds.LevelRaisingOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaBOfComponents
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferProductMonic
import Formalism.HermitianCurvature.StatementB
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.FormalDegreeBessel.FinalG
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
import Formalism.HermitianCurvature.StatementTC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities

section PartSl1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section Head

variable (k j r' : ℕ)

def slMid (p : Fin (2 * (j + r') + k + 1)) : Prop := j ≤ p.val ∧ p.val < 2 * r' + k + 1 + j

variable {k j r'}

variable (z z' : Fin (2 * (j + r') + k + 1) → ℂ) (h : Matrix (Fin j) (Fin j) ℂ)
  (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end Head

end Formalism.MainNotions.BridgeLemma₅

end PartSl1

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartBlk

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section GlobalTheory

variable {k j r' : ℕ}

instance slMid_dec (p : Fin (2 * (j + r') + k + 1)) : Decidable (slMid k j r' p) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (o o' : Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ)
  (g g' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end GlobalTheory

end Formalism.MainNotions.BridgeLemma₅

end PartBlk

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartWdAll

noncomputable section PartWd1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

section WdAbstract

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def wdCol (D : Set (Fin m → ℂ)) (O : Op m E) {n : ℕ} (M : Mod m E n) (Y : ℂ) : Prop :=
  ∀ (γ : AuxiliarySlotStates n) (f : (Fin m → ℂ) → E), ∀ x ∈ D, M.TT Y (0, γ) (0, e1s n) f x = if γ = e1s n then O f x else 0

end WdAbstract

end Formalism.MainNotions.BridgeLemma₅

end PartWd1

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end PartWdAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartFrAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartFr3

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.I

section Ring

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

noncomputable def frEv (Y : ℂ) : A[X] →+* A :=
  Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A Y) (fun a => (Algebra.commutes Y a).symm)

theorem frEv_apply (Y : ℂ) (P : A[X]) : frEv Y P = P.eval₂ (RingHom.id A) (algebraMap ℂ A Y) := rfl

@[simp] theorem frEv_X (Y : ℂ) : frEv (A := A) Y X = algebraMap ℂ A Y := by simp [frEv_apply]

@[simp] theorem frEv_C (Y : ℂ) (a : A) : frEv Y (C a) = a := by simp [frEv_apply]

end Ring

end Formalism.MainNotions.BridgeLemma₅

end PartFr3

section PartFr4

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators Formalism.MainNotions.LevelRaisingOperators
open scoped ContDiff

section Level

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ}

variable (C : Ctx B r) (Γ : GCtx E r)

def frLev0Open (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  (∀ n (hn : n ≤ r), ∀ Y : ℂ,
    let u := Y + ((Γ.nV : ℂ) - 1) / 2
    Γ.cminor n hn u ∈ Γ.PolyInv ∧ Γ.Rad (Γ.cminor n hn u) (DnVn n hn Y 0) ∧
    (∀ hn1 : n + 1 ≤ r, Γ.Rad (Γ.cminor n hn u) (DnVn (n + 1) hn1 Y 1))) ∧
  (∀ Y : ℂ, ∃ Θ ∈ Γ.PolyInv, Γ.Rad Θ (Rhat r C.Q Y)) ∧
  (∀ l, SSnat (SS l) ∈ C.AA) ∧ (∀ Y : ℂ, R0 r B.T B.T' h Y ∈ C.AA) ∧
  (∀ Y : ℂ, NoPoleRho B Y →
    C.OpEq (R0 r B.T B.T' h Y)
      (mulE (xInvFib B.rhoP C.P Y) ∘ Rhat r C.Q Y -
        ∑ l, mulE (shInv B.rhoP C.P l Y) ∘ SSnat (SS l) ∘ Ahat r Y)) ∧
  (∀ Y : ℂ, NoPoleRho B Y →
    C.OpEq (mulE (xInvFib B.rhoP C.P Y) ∘ C.RhatV Y)
      (weightedMirrorLevelOperator r B.T B.T' (C.fstar h) Y +
        ∑ l, mulE (shInv B.rhoP C.P l Y) ∘ (mulF (fun x => Dr x / star (Dr x)) ∘ mulE (C.fstar (SS l))) ∘ AhatV r Y))

end Level

end Formalism.MainNotions.BridgeLemma₅

end PartFr4

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartFr6

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators Formalism.MainNotions.LevelRaisingOperators

section Res

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ} (C : Ctx B r)

variable {C}

variable (C)

def frResOpen (C1 C2 : ℝ) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  ∀ w : List (Bool × ℝ), Admissible B.I w → Ctx.IsPlus w → (∀ a ∈ w, a.2 ∈ mid3 B) →
    (6 ≤ lenI B → (w.length : ℝ) ≤ lenI B →
      (∀ i : Fin w.length, (∑ j : Fin w.length, if j = i then 0 else 1 / |(w.get i).2 - (w.get j).2|) ≤ C1) →
      ∀ Y Y' : ℝ, Y ∈ mid3 B → Y' ∈ mid3 B → (∀ a ∈ w, 2 < |Y - a.2| ∧ 2 < |Y' - a.2|) →
      (w.map fun a => 1 / |Y - a.2|).sum ≤ C1 → (w.map fun a => 1 / |Y' - a.2|).sum ≤ C1 →
      ∀ x ∈ C.Dom, ∀ v : (Fin w.length → Fin 2) → E,
        wnormSq C (fun s ρ => C.cw w s ρ * C.xw w Y s ρ) x
            (fun s => ∑ t, (C.ee SS w Y s t x - C.ee SS w Y' s t x) (v t)) ≤
          (C2 * |Y - Y'| * ((B.k0 + 1 : ℝ) / lenI B + (w.map fun a => 1 / (|Y - a.2| * |Y' - a.2|)).sum)) ^ 2 *
            wnormSq C (fun s ρ => C.cw w s ρ * C.qw w Y / C.xw w ((Y : ℂ) + 1) s ρ) x v)

end Res

end Formalism.MainNotions.BridgeLemma₅

end PartFr6

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end PartFrAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartLb4

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lb_haarG : Formalism.FourierDecayAlt.B2.HaarGExists :=
  (Formalism.FourierDecayAlt.P.group_measure_from_diagonal Formalism.REAL.uJEmb Formalism.REAL.unimodular Formalism.REAL.ballFinite Formalism.REAL.volGrowth
    Formalism.QuantumDeterminants.hpkFacts Formalism.QuantumDeterminants.uHConj Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar Formalism.FourierDecayAlt.P.unitary_group_closed).1

def lbHaarUp : Prop :=
  (∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) ∧
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (Nset k r) μ → Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μ

def lbRepOfHC : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHCTypeW k r z u π →
      IsCRepOn (UWset k r z) π ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ ContinuousOn π (UWset k r z)

end Formalism.MainNotions.BridgeLemma₅

end PartLb4

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartTaAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

section PartTa4

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt.TA Formalism.MainNotions.InterlacingSignCuts

attribute [local instance] Classical.propDecidable

def ThmAHyp (D : D7) (C : ℝ) (Kst : ℕ) (δ : D.host.E) (T T' : ℝ) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
    (B : D.what₂.Tau → LocBessel D.R.k D.R.rS)
    (f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp))
    (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  4 ≤ Kst ∧ 1 ≤ D.host.v ∧ PsiAx D δ ∧ LatAx D δ L ∧ FrameAx D δ L B ∧ ArithAxF D L Kd ∧
    (∀ v, LocMatch D T T' (x v) (B v) ∧ IsKFinCoefH (B v).σ (f v) ∧
      IsSection D.R.k D.R.rS (B v).z (B v).z' (μsec v)) ∧
    (∀ v, InterlaceS (k_le_nS D) (x v).u (x v).lam ∧ InterlaceS (k_le_nS D) (x v).u' (x v).lam) ∧
    (∀ v, (x v).u ≠ (x v).u') ∧
    (∀ v, GapAtLeast (epsSH D.R) (x v).lam
      (C * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Kst * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3))) ∧
    (∀ v, IsCutS (x v).u (x v).u' (Set.Icc (x v).a (x v).b)) ∧
    (∀ v, (x v).a ≤ (x v).a1 ∧ (x v).a1 ≤ (x v).b1 ∧ (x v).b1 ≤ (x v).b ∧
      Nlet D Kst ^ 3 / 2 ≤ (x v).b1 - (x v).a1) ∧
    (∀ v, C * ((D.R.k : ℝ) * Nlet D Kst * ((D.R.rS : ℝ) + 1) ^ 2 +
        Nlet D Kst ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + Nlet D Kst ^ 3) ≤ (x v).b - (x v).a)

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa4

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end PartTaAll

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

