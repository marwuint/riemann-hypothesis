import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ArchimedeanCocycleCharacter
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValueBelow
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaDictCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Unif

variable {r : ℕ}

def toU {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  @Formalism.L2.Pj.Unf.mk _ _ _ _ _ _ _ Xo c σ r U.Comp U.fin U.X U.un

end Unif

def SameVal (f f' : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c f' y

section Down

variable {n : ℕ}

def FacTie (d : DeltaDat Xo c n) (cξ : Rul Xo c) (cδ' : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y →
      evR d.Xo₂ d.c₂ cδ' y₂ = evR Xo c cξ y * evR d.Xo₂ d.c₂ d.cδ y₂

variable {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
  {ι : Type} [Fintype ι]

end Down

section Act

variable {G0 : Type} [Group G0]

def CentreTie (e : G0 → LevGrp Dw l) : Prop :=
  (∀ z ∈ Subgroup.center G0, e z ∈ Subgroup.center (LevGrp Dw l)) ∧
    ∀ κ ∈ Subgroup.center (LevGrp Dw l), ∃ z ∈ Subgroup.center G0, e z = κ

def ActTie (e : G0 → LevGrp Dw l) (act : G0 → Rul Xo c →ₗ[c.F] Rul Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ z ∈ Subgroup.center G0, ∀ f ∈ sec Xo c a n, ∀ f' : Rul Xo c, IsLevelAct (e z) f f' ↔ SameVal f' (act z f)

end Act

section Row

variable {D : D7} (V : HSp D) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ)
  (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) (xi : ℝ)
  (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ}
  {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
  {Tup : Type} (d : Tup → DeltaDat Xo c n) {ι : Tup → Type} [∀ t, Fintype (ι t)] (vol : Tup → ℚ)
  (J : Tup → Subgroup (UA E n)) (h : ∀ t, ι t → UA E n) (N : ∀ t, ι t → ℕ) (ep : Tup → UA E n → ℂ)
  (cξ : Tup → Rul Xo c) (φ : Tup → (Fin n → ConjQ Dw l) → c.F) (φδ : ∀ t, (Fin n → LaJ Xo c (d t)) → c.F)
  (dd : (E →+* ℂ) → ℤ) (lam : ∀ t, J t →* c.Fˣ) (thB : Tup → (UA E n → T) → GA D V → ℂ)
  (q₁ : ℕ) (S : Tup → Finset (Plc E))
  {G0 : Type} [Group G0] (e : G0 → LevGrp Dw l) (act : G0 → Rul Xo c →ₗ[c.F] Rul Xo c)
  (cδ' : ∀ t, Rul (d t).Xo₂ (d t).c₂) (w : ∀ t, ι t → (Fin n → LevQ Dw (d t).l₂) → c.F) (κ : ∀ t, ι t → c.F)
  (thA : ∀ t, (ι t → T) → AutQ V → ℂ) (Pl : ∀ t, (ι t → T) → Prop)

structure Ties : Prop where
  centre : CentreTie e
  level : ActTie e act a n
  keeps : ∀ z ∈ Subgroup.center G0, ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, act z f ∈ Formalism.L2.PjFree.cusp Xo c U a n
  factor : ∀ t, FacTie (d t) (cξ t) (cδ' t)
  fourier : ∀ t i q, (d t).eF (w t i q) = fourierSum (d t).c₂ (coverDatum (d t) (φ t) (φδ t)) q
  scalar : ∀ t i, IsScalar (Dw := Dw) c (ep t) (h t i) (κ t i)
  placed : ∀ t x, Pl t x ↔ ∃ f, IsPlaced c dd (lam t) io f ∧ x = fun i => f (h t i)
  lift : ∀ t f, IsPlaced c dd (lam t) io f → ∀ g, thB t f g = thA t (fun i => f (h t i)) (Quotient.mk _ g)

variable {V U σ dict mu xi a io d vol J h N ep cξ φ φδ dd lam thB q₁ S e act cδ' w κ thA Pl}

end Row

end GlobalTheory.ThetaDictCompare
