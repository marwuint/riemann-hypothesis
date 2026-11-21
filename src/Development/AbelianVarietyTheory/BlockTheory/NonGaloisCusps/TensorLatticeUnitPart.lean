import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (i.f.coprod i'.f) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

variable (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def UnitAt (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one, E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun a : W.EE => a • e) ∧
      W.φD W.one e = e ∧ (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

def UnitPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    UnitAt (H.W K s LL h) (F.E K s LL h).tie

end GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
