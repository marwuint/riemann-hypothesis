import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Core

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Ops

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def mulPeriod (b : BdR) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

def mapdR {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR :=
  AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)

def tdR : BdRˣ := (PD.t_unit.map PD.ι).unit

variable (ρ : Representation LL G V)

def filDdR (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) := DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a

def jumpMult (τ : K →ₐ[Qp] LL) (a : ℤ) : ℕ :=
  Module.finrank LL (↥(FildR PD ρ τ a) ⧸ (FildR PD ρ τ (a + 1)).comap (FildR PD ρ τ a).subtype)

end Ops

variable [TopologicalSpace G] (LL O : Type) [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL]

def CrysDeRhamCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → IsDR PD T.ρ

def SpanCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    DdR PD T.ρ = ⨆ c : K, ((Dcris PD T.ρ).map (ιV PD (LL := LL) (V := T.V))).map
      (mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) c)

def StrictCore : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (f : T₀.V →ₗ[LL] T₁.V) (g : T₁.V →ₗ[LL] T₂.V),
    (∀ s x, f (T₀.ρ s x) = T₁.ρ s (f x)) → (∀ s x, g (T₁.ρ s x) = T₂.ρ s (g x)) →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsDR PD T₀.ρ → IsDR PD T₁.ρ → IsDR PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (∀ x ∈ FildR PD T₀.ρ τ a, mapdR (Qp := Qp) (BdR := BdR) f x = 0 → x = 0) ∧
      (FildR PD T₀.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) f) =
        FildR PD T₁.ρ τ a ⊓ LinearMap.ker (mapdR (Qp := Qp) (BdR := BdR) g) ∧
      (FildR PD T₁.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) g) = FildR PD T₂.ρ τ a

end Core

section Local

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

def CrysDeRham : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → CrysDeRhamCore (P.PD K) ↥LL.1 ↥(OL LL)

def Strictness : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → StrictCore (P.PD K) ↥LL.1 ↥(OL LL)

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual
