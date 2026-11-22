import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenCompactLevelThetaKernelBottomTriple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder

open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal

namespace GlobalTheory.RowTest.BottomClassSum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem weil' (hX : IsBottomTri W i j X) (t : T) :
    IsWeilDatumO W.ψ A' WW (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.ω' t) :=
  hX.is.weil' t

theorem theta' (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) :
    IsThetaFunO W.ψ A' WW (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO hX.is.isVac'.1 hX.is.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
    (GlobalTheory.ConstRatio.theta_f hX.is t).2 P

theorem ker'_left (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) :
    ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
  intro γ hγ g
  have hW := weil' hX t
  have hF := theta' hX t P
  show X.ω' t (γ * g, h) _ 0 = X.ω' t (g, h) _ 0
  have e : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hF)

theorem ker'_cont (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) (x : GA D A') :
    Continuous fun k : GinfC A' => X.ker' W.ψ W.θ t P h (x * k) := by
  have hW := weil' hX t
  have hF := theta' hX t P
  exact (hW.om_cont _ hF 0).comp ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)

theorem level_all [Finite T] (t₀ : T) (hX : IsBottomTri W i j X) :
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  choose K hK hinv using _root_.GlobalTheory.BotKerLevel.exists_level hX
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A'
  have hG := hT.2.2.2.2.1
  refine ⟨⨅ t, K t, ⟨?_, ?_⟩, fun t P h k hk g => hinv t P h k ?_ g⟩
  · have e : (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) =
        ⋂ t, (((K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
      ext x; simp [Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hK t).1
  · have hcl : IsClosed ((((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A'))) := by
      have e : (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) =
          ⋂ t, (((K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
        ext x; simp [Subgroup.mem_iInf]
      rw [e]
      exact isClosed_iInter fun t => Subgroup.isClosed_of_isOpen _ (hK t).1
    have e2 : ((Lev.levA A' (⨅ t, K t) : Subgroup (GA D A')) : Set (GA D A')) =
        (Lev.levA A' (K t₀) : Set (GA D A')) ∩ (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Lev.mem_levA, Subgroup.mem_comap]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, (Subgroup.mem_iInf.1 h2) t₀⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [e2]
    exact (hK t₀).2.inter_right hcl
  · obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨hk1, (Subgroup.mem_iInf.1 hk2) t⟩

end GlobalTheory.RowTest.BottomClassSum
