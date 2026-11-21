import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

section Defs

variable {O G VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT']

def pairF (D : LatData O G VT VT') : H1 D.ρT →ₗ[O] H1 D.ρT' →ₗ[O] FractionRing O :=
  (cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT').compr₂ D.invF

def withInv (D : LatData O G VT VT') (inv : H2 (twist D.ε (KO O)) →ₗ[O] KO O)
    (invF : H2 (twist D.ε (FractionRing O)) →ₗ[O] FractionRing O) : LatData O G VT VT' :=
  { D with inv := inv, invF := invF }

end Defs

structure RealData {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT') : Prop where
  cyc : IsCyc p K D.ε
  lat : IsLatticeIn D.T
  perf : PerfectRight D.bT
  contT : ContAction D.ρT
  openT : IsOpen (D.T : Set VT)
  t2 : T2Space VT
  t2' : T2Space VT'
  cs : ContinuousConstSMul (FractionRing O) VT
  cs' : ContinuousConstSMul (FractionRing O) VT'

def StatFinGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT'),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → RealData D → Module.Finite O (H1 D.ρTl')

def StatIntGK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (D : LatData O (GK p K) VT VT'),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → RealData D → Function.Injective D.inv →
    ∀ x, (∀ t, D.pr x t = 0) → x = 0

def StatCompat : Prop :=
  ∀ (O G VT VT' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT'), D.InvCompat →
    ∀ a t, D.pr (D.q a) t = Submodule.Quotient.mk (pairF D a (D.j' t))

end Formalism.RepresentationBoundsCohomology.T2
