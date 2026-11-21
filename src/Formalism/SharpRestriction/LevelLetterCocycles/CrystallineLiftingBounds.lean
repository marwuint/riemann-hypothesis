import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingBounds

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachLatticeFreeLocal D.loc HW D.locA F

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2L D.loc HW D.locA F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p3L D.loc HW D.locA F Cm

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p4L D.loc HW D.locA F Cm

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p5L D.loc HW D.locA F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p6L D.loc HW D.locA F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p7L D.loc HW D.locA F

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p8L D.loc HW D.locA F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p9L D.loc HW D.locA F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachCharacterisationLocal D.loc HW D.locA F

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.gammaSemisimpleLocal D.loc HW D.locA F

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2aL D.loc HW D.locA F

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2bL D.loc HW D.locA F

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2cL D.loc HW D.locA F

def adm15 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.p2dL D.loc HW D.locA F

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.wachLengthLocal D.loc HW D.locA F

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem invariant_cocycle_le_gamma_cocycle (W : LocWach PD LL O v n) (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) :
    W.wachCocyclesDelta T ≤ W.divisibleCocycles T := by
  have e := W.gamK_eq_one h1 h2
  intro x hx
  unfold Formalism.BasicNotions.LocWach.wachCocyclesDelta Formalism.BasicNotions.herrZ1Δ at hx
  have hx1 := (Submodule.mem_inf.mp hx).1
  rw [e] at hx1
  exact hx1

def coreResK (W : LocWach PD LL O v n) : Prop :=
  ∀ (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) (w : ↥(W.wachCocyclesDelta T)),
    Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (W.clK T w) =
      W.cl T ⟨(w : W.DD T × W.DD T), invariant_cocycle_le_gamma_cocycle W h1 h2 T w.2⟩

variable (PD LL O) in

def coreJumps : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → IsCrys PD T₀.ρ → IsCrys PD T₁.ρ → IsCrys PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      IsJumpV PD T₁.ρ τ a ↔ IsJumpV PD T₀.ρ τ a ∨ IsJumpV PD T₂.ρ τ a

end Local

def adm17 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreExt ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreExtΔ ((HW l).W K s LL h)

def adm19 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.LiftingTheory.coreDss ((HW l).W K s LL h)

def adm20 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (_hKK : K'.1 ≤ K.1) (hle : GK K ≤ GK K')
    (LL : FinExt l),
    Formalism.MainNotions.LiftingTheory.coreCor ((D.loc l).PD K) ((D.loc l).PD K') ↥LL.1 ↥(OL LL) (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _)
      (Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1)

def adm21 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ (s = 1 → l ≠ 2 → ((HW l).W K s LL h).ClKNat)

theorem resK_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : coreResK ((HW l).W K s LL h) := by
  intro h1 h2 T w
  exact ((F l).E K s LL h).tie.clK_res (((HW l).W K s LL h).gamK_eq_one h1 h2) T w _ rfl

def adm22 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), FontaineLe ((D.loc l).PD K) ↥LL.1

def adm23 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), coreJumps ((D.loc l).PD K) ↥LL.1 ↥(OL LL)

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  adm1 D HW F ∧ adm2 D HW F ∧ adm3 D HW F Cm ∧ ArchimedeanSignatureMatching D HW F Cm ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F ∧ adm8 D HW F ∧
    adm9 D HW F ∧ adm10 D HW F ∧ adm11 D HW F ∧ adm12 D HW F ∧ adm13 D HW F ∧ adm14 D HW F ∧ adm15 D HW F ∧ adm16 D HW F ∧
    adm17 D HW F ∧ adm18 D HW F ∧ adm19 D HW F ∧ adm20 D HW F ∧ adm21 D HW F ∧ adm22 D HW F ∧ adm23 D HW F

end Formalism.MainNotions.CrystallineLiftingBounds
