import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HaarOrderData

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup

namespace GlobalTheory.CompanionTheory.Sep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev PropG := ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {sc : Consts}
  {G : GridData R.toLevCh sc}, G.Weil → Vol G → Prop

def Big (P : PropG) : Prop :=
  ∀ ε CF : ℝ, 6510 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → SizeRows large₂ →
    GlobalTheory.GLq.ESerTie D →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
      R.toLevCh.Is A.μ0 → R.grp_record →
      ∀ (G : GridData R.toLevCh ⟨1, CF, large₂.sc.b⟩) (W : G.Weil), W.Over R → ∀ M : Vol G, M.IsRow → P R W M

end GlobalTheory.CompanionTheory.Sep

end
