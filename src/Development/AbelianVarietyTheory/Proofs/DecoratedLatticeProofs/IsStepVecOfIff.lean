import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.DoubledUnramifiedFrames
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RouteCompare

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def toFin (p : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank n) : Frame p S n :=
  ⟨F.β, F.γ, F.βγ, F.γβ, (GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose,
    fun g => ((GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose_spec g).1,
    fun g => ((GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose_spec g).2⟩

def move {p : SplitPt D k} {S : HSp D} (β : Frame p S n) (g : GA D S) : Frame p S n :=
  toFin p S ⟨(mt S g).map p.pr * β.b, β.b' * (mt S g⁻¹).map p.pr,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ β.b, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt, β.b'b]⟩

def JacCols {p : SplitPt D k} {ρ : ℕ} (J : JacLev D ρ) (θ s a : k) (α : Frame p J.W₀ n) (β : Frame p J.W (n ⊕ Fin c)) : Prop :=
  c = 2 * ρ ∧ (∀ r b, β.b r (Sum.inl b) = (J.d.i₀.map (ofSplit p).pr * α.b) r b) ∧
    (∀ (i : Fin ρ) (j : Fin c), j.val = i.val → ∀ r, β.b r (Sum.inr j) = s * θ ^ (ρ - i.val) * (ofSplit p).pr (J.d.e r i)) ∧
    ∀ (i : Fin ρ) (j : Fin c), j.val + i.val + 1 = 2 * ρ → ∀ r,
      β.b r (Sum.inr j) = s * a * (-1 / θ) ^ (ρ - 1 - i.val) * (ofSplit p).pr (J.d.e' r i)

end Local

open Classical in

def stepDat (c : GlobalTheory.ChainOnto.Com D) (s s' : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO s.V s'.V) : ℂ :=
  if IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x) then
    omegaG s.L (c.chi (j + 1)) (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x)) *
      omegaQ ∅ s.L.r ξ 1 (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
  else 0

variable {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

end GlobalTheory.RouteCompare

end
