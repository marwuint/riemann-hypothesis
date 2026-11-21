import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnitPairEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReindexIff

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open GlobalTheory.FinPl (SplitPt grpAt grpOff)
open GlobalTheory.SymCompare (sE)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.CompactOpenVolumes (places IsUnitPair put biPut volK IsCptOpen RowComb)

namespace GlobalTheory.QCmp

section Many
variable {D : D7} {I : Type} [Fintype I] [DecidableEq I] {k : I → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
  [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
variable {Y Y' : I → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] [∀ i, Fintype (Y' i)] [∀ i, DecidableEq (Y' i)]

def Emb (q : ∀ i, SplitPt D (k i)) (V : HSp D) (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i))
    (ι : (∀ i, GL (Y i) (k i)) → GA D V) : Prop :=
  ∀ x, ι x ∈ grpAt V (places q) ∧ ∀ i, (mt V (ι x)).map (q i).pr = (F i).β * (x i).val * (F i).γ

def Vacs (q : ∀ i, SplitPt D (k i)) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}
    (FS : ∀ i, GlobalTheory.LocMod.Frame (k i) S.rank (Y' i)) (FT : ∀ i, GlobalTheory.LocMod.Frame (k i) T.rank (Y i)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ i, ∃ Tm, (ofSplit (q i)).IsModel ψ (FS i) (FT i) Tm ∧ ∀ O, IsOne O → Tm O = f

end Many

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def Same (Q Q' : QStep S) : Prop :=
  Q'.q.v = Q.q.v ∧ (∀ x, IntAt Q'.q.v Q'.gl₁ x ↔ IntAt Q.q.v Q.gl₁ x) ∧ (∀ x, IntAt Q'.q.v Q'.gl₂ x ↔ IntAt Q.q.v Q.gl₂ x) ∧
    Q'.D₁ = Q.D₁ ∧ Q'.D₂ = Q.D₂ ∧ Q'.e₀.mapDomain Q'.gl₀ = Q.e₀.mapDomain Q.gl₀ ∧ Q'.volJ = Q.volJ ∧
    (∀ f₁ f₂, Q.Vac f₁ f₂ → Q'.Vac f₁ f₂) ∧ (∀ f, Q.Typed f → Q'.Typed f) ∧
    ∃ (a : Q.A₁ ≃ Q'.A₁) (b : Q.A₂ ≃ Q'.A₂), (∀ γ, Q'.w₁ (a γ) = Q.w₁ γ ∧ Q'.d₁ (a γ) = Q.d₁ γ) ∧
      (∀ β, Q'.w₂ (b β) = Q.w₂ β ∧ (Q'.e₂ (b β)).mapDomain Q'.gl₂ = (Q.e₂ β).mapDomain Q.gl₂) ∧
      ∀ γ β, Q'.d₂ (a γ) (b β) = Q.d₂ γ β

theorem Same.refl (Q : QStep S) : Same Q Q :=
  ⟨rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, fun _ h => h, Equiv.refl _, Equiv.refl _,
    fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

end GlobalTheory.QCmp
end
