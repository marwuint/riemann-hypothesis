import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingOfSg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffTwistedClass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTwistedClass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopValueWitness
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneFormExistsHeq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniform
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedLatticeOfAdelicMatrixEqRowPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemma

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

theorem isJ_smul {D : D7} {u : D.what₂.Word} {S : D.what₂.Tau → SPar} {M : Formalism.IndefR.Mult.DSModel D.sp.X' S}
    {j : SmT M →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)} (h : GlobalTheory.Core.Rk.Top.IsJ u M j) {a : ℂ} (ha : a ≠ 0) :
    GlobalTheory.Core.Rk.Top.IsJ u M (a • j) where
  inj := fun _ _ e => h.inj (smul_right_injective _ ha e)
  range := (LinearMap.range_smul j a ha).trans h.range
  eqv := fun τ g hg v w hw y y' hy => congrArg (a * ·) (h.eqv τ g hg v w hw y y' hy)

theorem levG_one {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad} (K : Formalism.L2.Forms.ClassesAtPrimes M bad)
    {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ} (h1 : ∀ g, g ∈ J ↔ ∃ κ : K.lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1)
    (h2 : ∀ g (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → χ g = star ((K.lev.chi κ : ℂˣ) : ℂ)) : LevG K 1 J χ := by
  simp only [LevG, inv_one, one_mul, mul_one]
  exact ⟨h1, h2⟩

end GlobalTheory.TopVal
