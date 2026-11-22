import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCombAtReN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.TopDatumTheta

open GlobalTheory.LocMod.StepVec
open GlobalTheory.FunObj.Comparison₂ (IsRed)

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_moved (p : Place D k) (GS : Frame k S.rank Y') (GT : Frame k T.rank Y) (g : GA D S) (h : GA D T) (x : WO S T) :
    p.down (moved p GS g) (moved p GT h) (actO S T g h x) = p.down GS GT x := by
  have h1 : (Formalism.L2.Theta.mt T h⁻¹).map p.π * (Formalism.L2.Theta.mt T h).map p.π = 1 := by
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt]
  have h2 : (Formalism.L2.Theta.mt S g⁻¹).map p.π * (Formalism.L2.Theta.mt S g).map p.π = 1 := by
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt]
  unfold Place.down moved
  rw [GlobalTheory.VacMove.actO_eq, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((Formalism.L2.Theta.mt T h⁻¹).map p.π), h1, Matrix.one_mul,
    ← Matrix.mul_assoc ((Formalism.L2.Theta.mt S g⁻¹).map p.π), h2, Matrix.one_mul]

theorem coords_moved (p : Place D k) (GS : Frame k S.rank Y') (GT : Frame k T.rank Y) {π' : Datum.EAf D →+* k}
    (hπ : ∀ a, π' (toEAf D a) = p.π a) {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (LS : LatFrame k ι' Y') (LT : LatFrame k ι Y) (ea : ι' ≃ Fin S.rank) (eb : ι ≃ Fin T.rank)
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {g : GA D S} {h : GA D T}
    (mS : MovedTo p S g βS ((GS.β * LS.bas.val).submatrix id fun i => LS.ord (ea.symm i)))
    (mT : MovedTo p T h βT ((GT.β * LT.bas.val).submatrix id fun i => LT.ord (eb.symm i))) (x : WO S T) :
    LT.coords LS (p.down GS GT x) = ((frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)).map π').submatrix eb ea := by
  rw [← coords_down p _ _ hπ LS LT ea eb (map_eq_of_movedTo _ GS hπ _ _ mS) (map_eq_of_movedTo _ GT hπ _ _ mT), down_moved]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (x : WO S T) : IsHalf e (actO S T g h x) ↔ IsHalf e x :=
  ⟨fun H => by
    have := GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ H
    rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this, GlobalTheory.SplitHecke.isHalf_actO g h⟩

theorem part_int (q : GlobalTheory.FinPl.SplitPt D k) {π' : Datum.EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = q.pr a)
    (hint : ∀ z : Datum.EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k]) {z : Datum.EAf D} (hz : π' z ∈ 𝒪[k]) :
    toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hee : q.e * q.e = q.e := q.split.1
  have h1 : q.pr q.e = 1 := by
    have a := (ofSplit q).ι_π 1
    have b := (ofSplit q).π_ι ((ofSplit q).π 1)
    rw [a, mul_one, map_one] at b
    exact b
  refine (hint _).2 ⟨?_, ?_⟩
  · rw [← mul_assoc, sub_mul, one_mul, ← map_mul, hee, sub_self, zero_mul]
    exact zero_mem _
  · rwa [map_mul, hπ, h1, one_mul]

theorem sum_part_mem {R R' ι : Type} [CommRing R] [CommRing R'] [Fintype ι] (φ : R →+* R') (A : Subring R') (a : ι → R) (z : R')
    (h : ∀ i, φ (a i) * z ∈ A) : φ (∑ i, a i) * z ∈ A := by
  rw [map_sum, Finset.sum_mul]
  exact sum_mem fun i _ => h i

theorem idem_eq {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ} (a : Fin n → AE D)
    (pl : Fin n ≃ P) (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i).1) : e = ∑ i, a i := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P, ← Equiv.sum_comp pl]
  exact Finset.sum_congr rfl fun i _ => (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ _ _ (hes _ (pl i).2) (ha i)).1 rfl

end Gen

end GlobalTheory.TopDatumTheta

end
