import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n)

def WachLatticeFree : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → wachFree W T

def WachLatticeDualClosed : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (P : T.V →ₗ[LL] T'.V →ₗ[LL] LL), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    wachDual W T T' P

def WachLatticeTensorClosed : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (b : T.V →ₗ[LL] T'.V →ₗ[LL] T''.V),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → IsCrys PD T''.ρ → wachTensor W T T' T'' b

def WachLatticeMonoidal : Prop := WachLatticeDualClosed W ∧ WachLatticeTensorClosed W

def WachCharacterisationLattice : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p10 W T

def WachTwistLattice : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (j : ℤ), IsCrys PD T.ρ → IsCrys PD T'.ρ → wachTwistIso W T T' j

def GammaSemisimpleQuotient : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    ∀ y : ℕ, 1 ≤ y → SSEig W T (invN W T (W.Q ^ y)) (W.N T)
      {c | ∃ a ∈ Jumps (PD := PD) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧ c = (uU W) ^ (-(a + j))}

theorem wach_first_lattice_iff : WachFreeDualTensor W ↔ WachLatticeFree W ∧ WachLatticeMonoidal W := Iff.rfl

theorem wach_tenth_iff : WachTwistCharacterisation W ↔ WachCharacterisationLattice W ∧ WachTwistLattice W := Iff.rfl

end Local

section Theory

def wachLatticeFreeLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachLatticeFree ((HW l).W K s LL h)

def wachCharacterisationLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachCharacterisationLattice ((HW l).W K s LL h)

def gammaSemisimpleLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    GammaSemisimpleQuotient ((HW l).W K s LL h)

end Theory

section Design

def WachLatticeFreeGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachLatticeFreeLocal D.loc HW D.locA F

def WachCharacterisation (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachCharacterisationLocal D.loc HW D.locA F

def gammaSemisimpleQuotientGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  gammaSemisimpleLocal D.loc HW D.locA F

end Design

end Formalism.MainNotions.DeltaInvariantLattices
