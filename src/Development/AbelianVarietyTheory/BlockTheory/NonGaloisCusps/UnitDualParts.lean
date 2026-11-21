import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.CoboundaryTransfers.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

def extMul {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']
    (m : M ⊗[O] M' →ₗ[O] M'') (x : R ⊗[O] M) (y : R ⊗[O] M') : R ⊗[O] M'' :=
  m.baseChange R ((AlgebraTensorModule.distribBaseChange O R M M').symm (x ⊗ₜ[R] y))

def extPair {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (β : M →ₗ[O] M' →ₗ[O] O) (x : R ⊗[O] M) (y : R ⊗[O] M') : R :=
  TensorProduct.rid O R (extMul R (TensorProduct.lift β) x y)

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (fun p : T.V × T'.V => i.f p.1 + i'.f p.2) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

def SumFor (W : LocWach PD LL O v n) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L), IsSumLat i i' →
      ∃ σ : (W.DD T × W.DD T') ≃ₗ[W.EE] W.DD T'',
        (∀ x y, σ (x, y) = W.map i x + W.map i' y) ∧
        (∀ x y, W.φD T'' (σ (x, y)) = σ (W.φD T x, W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (σ (x, y)) = σ (W.γD T g x, W.γD T' g y)) ∧
        ∀ x y, σ (x, y) ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T')

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def UnitFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one,
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun c : W.EE => c • e) ∧
      W.φD W.one e = e ∧
      (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}

end Generic

def UnitPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), UnitFor (F.E K s LL h).tie

def SumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), SumFor (H.W K s LL h)

end GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
