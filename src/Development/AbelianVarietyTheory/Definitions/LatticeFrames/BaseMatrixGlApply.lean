import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Formalism.LocalRingCardinality.PosOfIsomEmb

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

section Coord

variable {K : Type} [Field K] {Y : Type} [Fintype Y] [DecidableEq Y] (V : HSp D) (pr : AE D →+* K)
  (β : Matrix (Fin V.rank) Y K) (γ : Matrix Y (Fin V.rank) K) (βγ : β * γ = 1) (γβ : γ * β = 1)

def coordHom (βγ : β * γ = 1) (γβ : γ * β = 1) : GA D V →* GL Y K :=
  MonoidHom.toHomUnits
    { toFun := fun κ => γ * (mt V κ).map pr * β
      map_one' := by simp [Formalism.L2.Theta.mt, γβ]
      map_mul' := fun κ κ' => by
        have h : (mt V (κ * κ')).map pr = (mt V κ).map pr * (β * γ) * (mt V κ').map pr := by
          rw [βγ, Matrix.mul_one, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt]
        rw [h]; simp only [Matrix.mul_assoc] }

theorem coordHom_val (κ : GA D V) : (coordHom V pr β γ βγ γβ κ).val = γ * (mt V κ).map pr * β := rfl

theorem eq_coordHom_iff (κ : GA D V) (g : GL Y K) :
    (mt V κ).map pr = β * g.val * γ ↔ g = coordHom V pr β γ βγ γβ κ := by
  constructor
  · intro h
    refine Units.ext ?_
    rw [coordHom_val, h]
    calc g.val = (γ * β) * g.val * (γ * β) := by simp [γβ]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rintro rfl
    rw [coordHom_val]
    calc (mt V κ).map pr = (β * γ) * (mt V κ).map pr * (β * γ) := by simp [βγ]
      _ = _ := by simp only [Matrix.mul_assoc]

end Coord

section AtLevel

variable {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)

abbrev GX.lev0 {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) :=
  (H.S.T (Fin D.R.t)).lev 0 (H.s + 1) (Nat.zero_add _)

end AtLevel

structure Arith : Prop where
  unifT : ∀ i, valuation k ((o.p i).pr (incA D (((D.mem u).A.T : ℕ) : D.host.E))) = valuation k ((o.q.1 : 𝒪[k]) : k)
  oneG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D (((D.mem u).A.T : ℕ) : D.host.E)) - 1) < 1
  unifG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) =
    valuation (G PP).k (((G PP).S.ϖ : (G PP).kˣ) : (G PP).k)
  under : ∀ PP : a.c.Pg, (G PP).q.v = PP.1.under (𝓞 D.host.F)
  tame : ∀ v, GlobalTheory.FinPl.Tame D v
  unr : ∀ v, v ∉ a.c.S → CharUnramAt D a.c.η v ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → CharUnramAt D (a.c.μ j) v
  pos : ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef
  lz : a.Lz.SigOK ∧ a.Lz.IsPosDef

end GlobalTheory.SeeSaw

end
