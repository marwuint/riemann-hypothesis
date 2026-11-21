import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.LocalRingCardinality.DataTies
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

noncomputable section

namespace Formalism.MainNotions.LocalBesselAndTopKernel.TOP

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

def SelfDualLatticeNormCongruenceAt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (abelian₂ : Submodule M.L.O V), H.IsSelfDual abelian₂ →
  ∀ (T T' : F), (∃ u v : (𝒪[F])ˣ, ((u : 𝒪[F]) : F) = T ∧ ((v : 𝒪[F]) : F) = T') →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E), IsUnit Zh.det →
    Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det *
        M.L.cj (Zh.submatrix (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det) ≠ 0 →
    ((∃ t : Term V M r, t.abelian₂ = abelian₂ ∧ t.T = T ∧ t.T' = T' ∧ H.IsTerm t ∧ H.Zhat t.f t.f' = Zh) ↔
      ∀ a b, HermSp.ZZplusOf M Zh T T' a b ∈ M.R)

def FamilyVolumeFourth {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r k n : ℕ) (C : ℝ) : Prop :=
  ∀ (ϖ : 𝒪[F]), Irreducible ϖ →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  (∀ (t : Term V M r), H.IsGeneric t →
    |H.dens ϖ t.abelian₂ (H.gram (H.MMfam t)) - 1| ≤
      C * (2 * (r : ℝ) + 2) * (Nat.card 𝓀[F] : ℝ) ^ (-((k : ℤ) - 2 * r - 2))) ∧
  (∀ (t₁ t₂ : Term V M r), H.IsGeneric t₁ → H.IsGeneric t₂ → H.IsScalarPair t₁ t₂ →
    H.dens ϖ t₁.abelian₂ (H.gram (H.MMfam t₁)) = H.dens ϖ t₂.abelian₂ (H.gram (H.MMfam t₂)))

end Formalism.MainNotions.LocalBesselAndTopKernel.TOP

namespace Formalism.MainNotions.LocalBesselAndTopKernel.GLOB

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

def CNT {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (X : TermLoc D Y δ M u u') (c : ℝ) : Prop :=
  0 < c ∧
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
    {γ : D.s.Term u u' | D.s.generic γ ∧ D.s.ptOf γ = w}.Finite ∧
    (¬ TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) → ∀ γ : D.s.Term u u', D.s.generic γ → D.s.ptOf γ ≠ w) ∧
    ∀ _ : TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w),
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ γ₀ : D.s.Term u u', D.s.generic γ₀ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ₀) ≠ 0 →
      ∑' γ : {γ : D.s.Term u u' // D.s.generic γ ∧ D.s.ptOf γ = w ∧
          kind (D.s.ptOf γ₀) = kind w ∧ ∀ p, thCls X γ p = thCls X γ₀ p},
        (X.massT γ.1 : ℂ) * D.s.cTerm γ.1 =
      (n0 c (D.mem u).A.T (D.mem u').A.T w : ℂ) * (densT X ϖ γ₀ : ℂ) *
        BBG M δ (D.mem u).A.T (D.mem u').A.T w (kind (D.s.ptOf γ₀)) (thCls X γ₀) / autG M (thCls X γ₀)

end Formalism.MainNotions.LocalBesselAndTopKernel.GLOB

namespace Formalism.MainNotions.LocalBesselAndTopKernel.SW

end Formalism.MainNotions.LocalBesselAndTopKernel.SW

namespace Formalism.MainNotions.LocalBesselAndTopKernel

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hyp (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0

open Classical in

def gsFam (D : D7) (u u' : D.what₂.Word) : D.s.Pair u u' → ℂ := fun P =>
  if scalarP D.s P ∧ D.s.Gterm (D.s.pfst P) ≠ 0 ∧ D.s.Gterm (D.s.psnd P) ≠ 0 then D.s.pval P else 0

def Conclusion1 (D : D7) (CA CA' Ce : ℝ) : Prop :=
  let N : ℝ := NA D
  let r : ℝ := D.R.rS
  ∀ u u' : D.what₂.Word, u ≠ u' → Summable (gsFam D u u') ∧
  ∀ (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D),
    IsLocA D u u' x → IsLatGLOB D L →
    (∀ τ, IsCutS (uS D u τ) (uS D u' τ) (Set.Icc (x τ).a (x τ).b) ∧
      CA * ((D.R.k : ℝ) * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ (x τ).b - (x τ).a ∧
      (x τ).a ≤ (x τ).a1 ∧ (x τ).b1 ≤ (x τ).b ∧ N ^ 3 / 2 ≤ (x τ).b1 - (x τ).a1) →
    (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ) ≤ 1 → CA' ≤ ThA D CA u u' x L →
    genScal D u u' ≤ (1 + CA * (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ)) * (1 + eSum D Ce) *
      (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) *
      (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar

def projection_sandwich_lattice (D : D7) : Prop :=
  UnitaryVolumeMass.cTvA D

def MassRatio₂ (D : D7) (C1 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvB D C1

def kernel_index_full_lattice (D : D7) (C2 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvC D C2

def gram_det_kernel_dual_lattice (D : D7) (C3 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvD D C3

def MidVolumeChain (D : D7) (large₂ : SizeData₂ D) (ep0 CV : ℝ) : Prop :=
  UnitaryVolumeMass.cTvG D large₂ ep0 CV

def AdmittedWeylDimension : Prop :=
  ∀ (k' : ℕ) (u : Fin k' → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k') (Fin k') ℂ → (H →L[ℂ] H)), StrictAnti u → IsHCTypeU k' u π →
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k', (i.factorial : ℝ)

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

def FamilySchurFormalDegree (D : D7) : Prop :=
  UnitaryVolumeMass.stMassRatio D

def GL5LogLValueBoundByZeta (D : D7) : Prop :=
  ∀ i : ℕ, 3 ≤ i →
    |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E i)| ≤ (D.R.f : ℝ) * Real.log (riemannZeta (i : ℂ)).re

def cardGL (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (q ^ n - q ^ i)

def dimNS (D : D7) : ℕ := D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)

def idxRows (D : D7) : ℝ :=
  ∏ᶠ p ∈ typedPl D, cardGL (Ideal.absNorm p.asIdeal : ℝ) D.R.r /
    ((Ideal.absNorm p.asIdeal : ℝ) ^ dimNS D * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))

def FamilyMidVolume (D : D7) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
    (L : Submodule (𝓞 D.host.E) V), h.IsSymm →
    (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word,
      (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * gaG D *
        (∏ τ, vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (Tr D u ^ D.R.k - 1) ^ D.R.f) ∧
    (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r →
      D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * idxRows D * ∏ τ, D.dsig τ)

def nPl {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = true)).card
def nMi {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = false)).card

section One

open Formalism.MainNotions.S.LocalSplitGroups

def FamilyExpansionSecond (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  FamilySchurFormalDegree D → GL5LogLValueBoundByZeta D → FamilyMidVolume D → hyp D large₂ C0 C' Cl Cg cb Cu cT CT → projection_sandwich_lattice D
def SecondBoundHyp (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C1 : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MassRatio₂ D C1
def LocalTiedPairs (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT ep0 CV C3' : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MidVolumeChain D large₂ ep0 CV → gram_det_kernel_dual_lattice D C3'
end One

section Family

open Formalism.MainNotions.S.LocalSplitGroups

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def UnderF (C0 Cg cb Cu cT CT : ℝ) (P : ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → P (Fm.D x i) (Fm.L x i)

def SecondSizeStatement : Prop := ∀ x (i : Fm.Ix x), FamilySchurFormalDegree (Fm.D x i)
def BesselFormLine : Prop := ∀ x (i : Fm.Ix x), GL5LogLValueBoundByZeta (Fm.D x i)
def FamilyRanksHypothesis (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => FamilyMidVolume D
def FamilyBesselBoundFirstPart (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => projection_sandwich_lattice D
def TheoremThreePassage (C0 Cg cb Cu cT CT C1 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => MassRatio₂ D C1
def FamilyLowestKType (C0 Cg cb Cu cT CT C2 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => kernel_index_full_lattice D C2
def LocalSplitExponents (C0 Cg cb Cu cT CT C3' : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => gram_det_kernel_dual_lattice D C3'
def FamilyTopBound (C0 Cg cb Cu cT CT ep0 CV : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D large₂ => MidVolumeChain D large₂ ep0 CV

def FamilyUnfoldingCount (C0 Cg cb Cu cT CT : ℝ) : Prop :=
  SecondSizeStatement Fm → BesselFormLine Fm → FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT → FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT

end Family

end Formalism.MainNotions.LocalBesselAndTopKernel
