import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingOfMinimal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingIntO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTowerHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartCocycleHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameMoveHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameOfFlagAt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

namespace Cht

open FamPf

theorem exists_fam : FamSt := by
  intro D A N j S κ p ct Z C y K w hw
  have hE : ExtendSt := extendSt
  have hF : FlagBaseSt := FlagBase.flagBase
  have hM : FrameMoveSt := frameMove
  have hC : CocycleSt := Cocycle.cocycle
  have hT : TowerSt := Tower.tower
  have hN : N2 ct.Y := (S.sys.clauses p ct.W ct.hp ct.hW).1
  have h1 : 1 ≤ S.Dw.p + S.Dw.q := by
    rw [S.rank_eq]; exact one_le_two.trans S.two_le
  obtain ⟨P, hP1, hP⟩ := hT _ _ _ _ _ _ ct.Y ct.hp ct.hW h1 C Z.i y.P
  have hyg : y.gen ≫ Z.π = (P Z.i).x0 := by
    have e : (P Z.i).x0 = spMap (intO ↥C.S).subtype ≫ (P Z.i).yt := (P Z.i).ext.symm
    rw [e, hP1, ← y.z_π, PtAt.gen, Category.assoc]
  have hr : Set.range w ⊆ Z.opn := by
    refine range_of_base K.subtype _ ?_
    rw [hw]
    rintro _ ⟨s, rfl⟩
    refine ⟨(P Z.i).y s, ?_⟩
    exact (congrArg (fun f => f s) hyg).symm
  obtain ⟨u₁, hu₁⟩ := ((hF _ _ _ _ _ _ ct.Y _ Z ↥K w).1 hr)
  have hu : Z.FlagAt y.gen (u₁.bc K.subtype) := by
    rw [← hw]
    exact (hF _ _ _ _ _ _ ct.Y _ Z ↥K w).2 ↥C.S K.subtype _ hu₁
  obtain ⟨fam, hfam, hall⟩ := fam_core hE hM hC hN P hP Z y hP1.symm _ hu
  refine ⟨fam, hfam, ?_⟩
  have hi : ct.YY.i = idx0 ct := ct.isYY.1.trans (ct.B.lvl none)
  have hd : ct.YY.i.l.Dvd Z.i.l := hi ▸ Z.dvd
  have hc : ct.YY.i.c.F ≤ Z.i.c.F := hi ▸ Z.le
  obtain ⟨mu, ht⟩ := exists_isTrans hN ct.YY.i Z.i hd hc
  obtain ⟨hg, hf⟩ := hall ct.YY _ mu hd ht
  exact rat_core hE hF hM K Z ct.YY hc ht (P Z.i) (P ct.YY.i) (hP _ _ _ _ hd ht) w (by rw [hw]; exact hyg) u₁ hu₁ _ hg hf

end Cht

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem Cht.genEx (ct : At S κ p) : Cht.GenEx ct :=
  Cht.genEx_of GlobalTheory.SpecialStalk.stalkSt Cht.CompletedClosure.fieldSt Cht.extendSt Cht.exists_fam ct

end GlobalTheory.LocM
