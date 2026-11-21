import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

def CobF : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) [TopologicalSpace G] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousConstSMul LL V],
    (∀ x, Continuous fun g => ρ g x) → B1 ρ ≤ finiteCocycles PD ρ ∧ finiteCocycles PD ρ ≤ continuousCocycles ρ

def TorsFreeT : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V) [TopologicalSpace G] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (c : G → V) (a : O),
    c ∈ latticeCocycles L → algebraMap O LL a ≠ 0 → a • c ∈ latticeFiniteCocycles PD L → c ∈ latticeFiniteCocycles PD L

def CocyclesFunctorial : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    (f : V →ₗ[LL] V'), Continuous f → (∀ g x, f (ρ g x) = ρ' g (f x)) →
    ∀ c, (c ∈ continuousCocycles ρ → f ∘ c ∈ continuousCocycles ρ') ∧ (c ∈ finiteCocycles PD ρ → f ∘ c ∈ finiteCocycles PD ρ')

def ImFLe : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul LL V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (F : LatHom L L'),
    (∀ x, Continuous fun g => ρ' g x) → F.ImF PD ≤ latticeFiniteCocycles PD L' ∧ (F.col PD = 0 ↔ F.LiftF PD 0)

def TrivCrys : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    [FiniteDimensional Qp LL] [FiniteDimensional Qp K₀],
    IsCrys PD (1 : Representation LL G LL)

def ExLattice : Prop :=
  ∀ (G : Type) [Group G] (LL : Type) [Field LL] (O : Type) [CommRing O] [IsDomain O]
    [Algebra O LL], Function.Injective (algebraMap O LL) →
    Nonempty (Lattice (O := O) (1 : Representation LL G LL))

def ExPD : Prop :=
  Nonempty (PeriodData (Multiplicative ℤ) ℚ ℚ ℚ (LaurentPolynomial ℚ) (LaurentPolynomial ℚ))

def WachCol : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (F : LatHom L L')
    (A D D' : Type) [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
    (Bw : Formalism.CoboundaryTransfers.Base O A) (M : ℕ) (W : Formalism.CoboundaryTransfers.WachMod Bw M D)
    (W' : Formalism.CoboundaryTransfers.WachMod Bw M D') (Fw : Formalism.CoboundaryTransfers.Hom W W')
    (cl : W.Z1 →ₗ[O] LatticeCohomology L) (cl' : W'.Z1 →ₗ[O] LatticeCohomology L'),
    Bw.p = PD.p → WachLink PD L W cl → WachLink PD L' W' cl' →
    (∀ (pr : W.Z1) (pr' : W'.Z1), (pr' : D' × D') = Fw.f2 pr → F.H1map (cl pr) = cl' pr') →
    F.col PD = Fw.col ∧ ∀ e, F.LiftF PD e ↔ Fw.LiftF e

end Formalism.WeaklyAdmissibleFiltrations
