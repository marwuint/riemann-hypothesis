import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains

noncomputable section

namespace Formalism.MainNotions.HerrCohomologyExtensions

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Ties

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def UnitGen (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  e ∈ W.N W.one ∧ W.N W.one = Submodule.span (LetA O n) {e} ∧
    Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
    W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ W.one.L.T = Submodule.span O {e₀}

def clsK (T : LocLat G Qp LL O) (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L) : LatticeCohomology T.L :=
  Submodule.Quotient.mk (⟨κ, hκ⟩ : ↥(latticeCocycles T.L))

def IsCocOf {T Tp : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (e₀ : W.one.V) (κ : G → T.V) : Prop :=
  IsSESLat (Qp := Qp) ι π ∧ ∃ t ∈ Tp.L.T, π.f t = e₀ ∧ ∀ g, ι.f (κ g) = Tp.ρ g t - t

def ExtKs (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    ∀ (x : W.DD Tp) (c : O), W.map π x = c • e →
    ∀ w : ↥(W.divisibleCocycles T), W.map ι (w : W.DD T × W.DD T).1 = W.φD Tp x - x →
      W.map ι (w : W.DD T × W.DD T).2 = W.γ Tp x - x →
      W.cl T w = c • Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (clsK T κ hκ)

def ExtK (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  W.s = 1 → PD.p ≠ 2 →
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    ∀ (x : W.DD Tp) (c : O), W.map π x = c • e → (∀ δ ∈ W.DelF, W.γD Tp δ x = x) →
    ∀ w : ↥(W.wachCocyclesDelta T), W.map ι (w : W.DD T × W.DD T).1 = W.φD Tp x - x →
      W.map ι (w : W.DD T × W.DD T).2 = W.γD Tp W.gamK x - x →
      W.clK T w = c • clsK T κ hκ

def HerrExt : Prop :=
  ∃ (e : W.DD W.one) (e₀ : W.one.V), UnitGen W e e₀ ∧ ExtKs W e e₀ ∧ ExtK W e e₀

end Ties

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrExt ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ Formalism.MainNotions.DeltaInvariantLattices.ClKNatG ((HW l).W K s LL h)

end Formalism.MainNotions.HerrCohomologyExtensions
