module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCharactersExtendedDataEqMapSmallerData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandraStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCopiesReferenceObjectsOverEnlargedBase, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersEStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormGroupsModelsActionsMeasuresBasesCharacterise, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBase, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBaseStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBaseStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDefiniteFormsLargerFieldCombinationSmall, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleHilbertModelDefiniteFormsEnlarged, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleWeilDatumVectorPolynomialMapEnlarg, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBaseStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBase, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBaseStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCopiesReferenceObjectsOverEnlargedBase =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCopiesReferenceObjectsOverEnlargedBase", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.WeilExt.RefType

private abbrev MM {Tau : Type} {n : ℕ} (H : Tau → Type) (na : ∀ τ, NormedAddCommGroup (H τ)) (ip : ∀ τ, InnerProductSpace ℂ (H τ))
    (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (fr : Tau → Matrix (Fin n) (Fin n) ℂ)
    (lie : Tau → Set (Matrix (Fin n) (Fin n) ℂ)) (X : Type) : Type :=
  MultilinearMap (RingHom.id ℂ) (fun τ : Tau => (Submodule.span ℂ {w | SmoothVec (lie τ) (fun g => σ τ (fr τ * g * (fr τ)⁻¹)) w} : Submodule ℂ (H τ)))
    (X → ℂ)

private theorem core {Tau Tau' : Type} {n n' : ℕ} {H : Tau → Type} {na : ∀ τ, NormedAddCommGroup (H τ)} {ip : ∀ τ, InnerProductSpace ℂ (H τ)}
    {σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)} {fr : Tau → Matrix (Fin n) (Fin n) ℂ}
    {lie : Tau → Set (Matrix (Fin n) (Fin n) ℂ)} {X : Type}
    {H' : Tau' → Type} {na' : ∀ τ, NormedAddCommGroup (H' τ)} {ip' : ∀ τ, InnerProductSpace ℂ (H' τ)}
    {σ' : ∀ τ, Matrix (Fin n') (Fin n') ℂ → (H' τ →L[ℂ] H' τ)} {fr' : Tau' → Matrix (Fin n') (Fin n') ℂ}
    {lie' : Tau' → Set (Matrix (Fin n') (Fin n') ℂ)} {X' : Type}
    {G G' C C' : Type} {nc : NormedAddCommGroup C} {ic : InnerProductSpace ℂ C} {nc' : NormedAddCommGroup C'} {ic' : InnerProductSpace ℂ C'}
    {HW : HMod (MM H na ip σ fr lie X)} {HW' : HMod (MM H' na' ip' σ' fr' lie' X')}
    (hT : Tau' = Tau) (hn : n' = n) (hlie : HEq lie' lie) (hX : X' = X) (hG : G' = G)
    (hC : HEq C' C) (hnc : HEq nc' nc) (hic : HEq ic' ic)
    (hH : HEq H' H) (hna : HEq na' na) (hip : HEq ip' ip) (hσ : HEq σ' σ) (hfr : HEq fr' fr) (hHW : HEq HW' HW)
    (K : HMod (G → C)) (th : K.H →ₗ[ℂ] MM H na ip σ fr lie X) (g : K.H →ₗ[ℂ] HW.H) :
    ∃ (K' : HMod (G' → C')) (th' : K'.H →ₗ[ℂ] MM H' na' ip' σ' fr' lie' X') (g' : K'.H →ₗ[ℂ] HW'.H),
      HEq K' K ∧ HEq th' th ∧ HEq g' g := by
  subst hT hn hX hG
  cases hlie; cases hC; cases hnc; cases hic; cases hH; cases hna; cases hip; cases hσ; cases hfr; cases hHW
  exact ⟨K, th, g, HEq.rfl, HEq.rfl, HEq.rfl⟩

private theorem mid {D D' : D7} {V W : HSp D} {V' W' : HSp D'} {L L' : Type} {S : L → D.what₂.Tau → SPar} {S' : L' → D'.what₂.Tau → SPar}
    (c : CoefA V) (c' : CoefA V') (M : ∀ s, Formalism.IndefR.Mult.DSModel W (S s)) (M' : ∀ s, Formalism.IndefR.Mult.DSModel W' (S' s))
    (HW : ∀ s, HMod (Formalism.IndefR.Mult.MMap (M s))) (HW' : ∀ s, HMod (Formalism.IndefR.Mult.MMap (M' s)))
    {s t : L} {s' t' : L'} (e : t = s) (e' : t' = s')
    (hT : D'.what₂.Tau = D.what₂.Tau) (hn : W'.rank = W.rank) (hlie : HEq (lieAt W') (lieAt W)) (hX : GA D' W' = GA D W)
    (hG : (Bridge.Gf V' : Type) = Bridge.Gf V)
    (hC : HEq c'.W c.W) (hnc : HEq c'.nW c.nW) (hic : HEq c'.iW c.iW)
    (hH : HEq (M' s').H (M s).H) (hna : HEq (M' s').nacg (M s).nacg) (hip : HEq (M' s').ips (M s).ips) (hσ : HEq (M' s').σ (M s).σ)
    (hfr : HEq (M' s').fr (M s).fr) (hHW : HEq (HW' s') (HW s))
    (K : HMod (Bridge.Gf V → c.W)) (th : K.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (M t)) (g : K.H →ₗ[ℂ] (HW t).H) :
    ∃ (K' : HMod (Bridge.Gf V' → c'.W)) (th' : K'.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (M' t')) (g' : K'.H →ₗ[ℂ] (HW' t').H),
      HEq K' K ∧ HEq th' th ∧ HEq g' g := by
  subst e e'
  exact core (lie := lieAt W) (lie' := lieAt W') (X := GA D W) (X' := GA D' W') (HW := HW t) (HW' := HW' t')
    hT hn hlie hX hG hC hnc hic hH hna hip hσ hfr hHW K th g

private theorem types (X X' : Stages) (h : X'.B.toPre = X.B.toPre) (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i') :
    X'.toD7.what₂.Tau = X.toD7.what₂.Tau ∧ (Wc X'.toD7 i').rank = (Wc X.toD7 i).rank ∧ HEq (lieAt (Wc X'.toD7 i')) (lieAt (Wc X.toD7 i)) ∧
    GA X'.toD7 (Wc X'.toD7 i') = GA X.toD7 (Wc X.toD7 i) ∧ (Bridge.Gf (Vc X'.toD7 i') : Type) = Bridge.Gf (Vc X.toD7 i) ∧
    (GA X.toD7 (Vc X.toD7 i) × GA X.toD7 (Wc X.toD7 i) →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc X.toD7 i) (Wc X.toD7 i) → ℂ)) =
      (GA X'.toD7 (Vc X'.toD7 i') × GA X'.toD7 (Wc X'.toD7 i') →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc X'.toD7 i') (Wc X'.toD7 i') → ℂ)) ∧
    (Formalism.IndefR.Datum.WO (Vc X.toD7 i) (Wc X.toD7 i) → ℂ) = (Formalism.IndefR.Datum.WO (Vc X'.toD7 i') (Wc X'.toD7 i') → ℂ) ∧
    Measure (GA X.toD7 (Vc X.toD7 i)) = Measure (GA X'.toD7 (Vc X'.toD7 i')) ∧
    Set (GA X.toD7 (Vc X.toD7 i)) = Set (GA X'.toD7 (Vc X'.toD7 i')) := by
  obtain ⟨B, C, W, V, S, N, G⟩ := X
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  cases B
  cases B'
  dsimp only at h
  subst h
  obtain ⟨i, hlt⟩ := i
  obtain ⟨i', hlt'⟩ := i'
  dsimp only at hi
  subst hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end GlobalTheory.Mem.R3.Rw.WeilExt.RefType

open GlobalTheory.Mem.R3.Rw.WeilExt.RefType in

theorem _root_.GlobalTheory.T.exists_copies_reference_objects_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSideW z Wt' R' → ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
  ∃ (ω : GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i') × GA (w'.st Z').toD7 (Wc (w'.st Z').toD7 i') →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc (w'.st Z').toD7 i') (Wc (w'.st Z').toD7 i') → ℂ))
    (v : Formalism.IndefR.Datum.WO (Vc (w'.st Z').toD7 i') (Wc (w'.st Z').toD7 i') → ℂ) (H : HMod (Bridge.Gf (Vc (w'.st Z').toD7 i') → (R'.cV i').W))
    (th : H.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (R'.MW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A))) (g : H.H →ₗ[ℂ] (R'.HW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)).H)
    (ν : Measure (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i'))) (fd : Set (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i'))),
    HEq ω (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq v (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq H (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq th (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq g (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq ν (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq fd (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hR i i' hi
  have hR' := hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi
  obtain ⟨hC, -, hnc, hic, -, -, -, hH, hna, hip, hσ, -, -, hfr, -, hHW, -⟩ := hR'
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := types (w.st Z) (w'.st Z') hE.1 i i' hi
  have key := mid (z.R.cV i) (R'.cV i') (z.R.MW i) (R'.MW i') (z.R.HW i) (R'.HW i')
    (sgAt_mk _ z.R.hv0) (sgAt_mk _ R'.hv0) t1 t2 t3 t4 t5 hC hnc hic hH hna hip hσ hfr hHW
    (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) (z.R.thF i _) (z.R.thG i _)
  obtain ⟨K, th, g, h1, h2, h3⟩ := key
  exact ⟨cast t6 (z.R.ωP i _), cast t7 (z.R.vP i _), K, th, g, cast t8 (z.R.νV i _), cast t9 (z.R.fdV i _), cast_heq _ _, cast_heq _ _,
    h1, h2, h3, cast_heq _ _, cast_heq _ _⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCopiesReferenceObjectsOverEnlargedBase =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.ChiWExt

section Move

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

theorem m_eq (hP : B'.toPre = B.toPre) : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  exact (by with_unfolding_all exact ((Eq.refl (w.st Z).toD7.R.m) :))

theorem gc_eq (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) : Gc B' px' = Gc B px := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  exact (by with_unfolding_all exact ((Eq.refl (Gc B px)) :))

theorem prod_move (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {Pg : Finset (Pl (w.st Z).toD7.host.E)} {Pg' : Finset (Pl (w'.st Z').toD7.host.E)} (hPg : HEq Pg' Pg)
    {eG : Gc B px ≃* G0 Pg (w.st Z).toD7.R.r} {eG' : Gc B' px' ≃* G0 Pg' (w'.st Z').toD7.R.r} (heG : HEq eG' eG)
    {χ : ∀ PP : Pl (w.st Z).toD7.host.E, (kP PP)ˣ →* ℂˣ} {χ' : ∀ PP : Pl (w'.st Z').toD7.host.E, (kP PP)ˣ →* ℂˣ}
    (hχ : ∀ PP' PP, HEq PP' PP → PP ∈ Pg → HEq (χ' PP') (χ PP)) {g : Gc B px} {g' : Gc B' px'} (hg : HEq g' g) :
    ∏ PP : Pg', ((χ' PP (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((χ PP (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (Pg')) ((by with_unfolding_all exact ((Pg) :))) (Pg') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Pg')) (Pg') (((Pg))) (((hPg)))).symm : _))
  clear (hPg)
  subst e))
  ( (
  have e : @Eq (type_of% (eG')) ((by with_unfolding_all exact ((eG) :))) (eG') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (eG')) (eG') (((eG))) (((heG)))).symm : _))
  clear (heG)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  have e : ∀ PP : Pl (w.st Z).toD7.host.E, PP ∈ Pg → HEq (χ' ((by with_unfolding_all exact (PP :)))) (χ PP) :=
    fun PP hm => hχ ((by with_unfolding_all exact (PP :))) PP ((by with_unfolding_all exact ((HEq.refl PP) :))) hm
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact congrArg (fun c : ℂˣ => (c : ℂ)) (DFunLike.congr_fun (eq_of_heq (e PP.1 PP.2)) _)

end Move



theorem grp_chiW_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → LevSame z Wt' R' → R'.toRealDat.grp_chiW := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hpx hS hL
  have hc := z.pins.char.base.grp.chiW
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  intro i' g'
  have hm := m_eq (w := w) (w' := w') (Z := Z) (Z' := Z') hE.1
  let i : Fin (w.st Z).toD7.R.m := ⟨i', by have := i'.2; omega⟩
  have hi : (i : ℕ) = i' := rfl
  let g : Gc B w.px := cast (gc_eq hE.1 hpx) g'
  have hg : HEq g' g := (cast_heq _ _).symm
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -, hW, -⟩ := hS'
  have hWi := hW i i' hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hWι⟩ := hWi
  have hch := (hWι ι hι).2.2.1 g' g hg
  rw [hch, hι, hc i g]
  exact (prod_move hE.1 hpx hPg heG (fun PP' PP h hm => (hL.1 i i' hi).2 PP' PP h hm) hg).symm

end GlobalTheory.Mem.R3.Rw.ChiWExt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersEStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersEStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

theorem _root_.GlobalTheory.T.finiteGroupCharacter_eq_product_residualCharacters_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → LevSame z Wt' R' → R'.toRealDat.grp_chiW := by
  first | exact @GlobalTheory.Mem.R3.Rw.ChiWExt.grp_chiW_ext
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersEStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormGroupsModelsActionsMeasuresBasesCharacterise =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormGroupsModelsActionsMeasuresBasesCharacterise", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.ModWExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Mem.R3.Rw.LiftExt

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {W : HSp a.D} {W' : HSp a'.D} {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}


private theorem is_of (hP : B'.toPre = B.toPre) (hW : HEq W' W) (h : DSTie M' M)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X)
    {U : Submodule ℂ (MMap M)} {U' : Submodule ℂ (MMap M')} (hU : HEq U' U)
    {ν : Measure (GA a.D W)} {ν' : Measure (GA a'.D W')} (hν : HEq ν' ν) {fd : Set (GA a.D W)} {fd' : Set (GA a'.D W')}
    (hfd : HEq fd' fd) (c : ℂ) (h0 : X.Is U fun T T' => c * ipM M ν fd T T') : X'.Is U' fun T T' => c * ipM M' ν' fd' T T' := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : W' = W := by with_unfolding_all exact eq_of_heq hW
  subst W'
  rcases M with @⟨H, nacg, ips, σ, lam, ε, fr, enum, ds, fu, fg⟩
  rcases M' with @⟨H', nacg', ips', σ', lam', ε', fr', enum', ds', fu', fg'⟩
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have : H' = H := by with_unfolding_all exact eq_of_heq h1
  subst H'
  have : nacg' = nacg := by with_unfolding_all exact eq_of_heq h2
  subst nacg'
  have : ips' = ips := by with_unfolding_all exact eq_of_heq h3
  subst ips'
  have : σ' = σ := by with_unfolding_all exact eq_of_heq h4
  subst σ'
  have : lam' = lam := by with_unfolding_all exact eq_of_heq h5
  subst lam'
  have : ε' = ε := by with_unfolding_all exact eq_of_heq h6
  subst ε'
  have : fr' = fr := by with_unfolding_all exact eq_of_heq h7
  subst fr'
  have : X' = X := by with_unfolding_all exact eq_of_heq hX
  subst X'
  have : U' = U := by with_unfolding_all exact eq_of_heq hU
  subst U'
  have : ν' = ν := by with_unfolding_all exact eq_of_heq hν
  subst ν'
  have : fd' = fd := by with_unfolding_all exact eq_of_heq hfd
  subst fd'
  exact (by with_unfolding_all exact (h0 :))

private theorem act_of (hP : B'.toPre = B.toPre) (hW : HEq W' W) (h : DSTie M' M)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {ρ : Representation ℂ G X.H} {ρ' : Representation ℂ G' X'.H} (hρ : HEq ρ' ρ)
    {L : G → (GA a.D W → ℂ) →ₗ[ℂ] (GA a.D W → ℂ)} {L' : G' → (GA a'.D W' → ℂ) →ₗ[ℂ] (GA a'.D W' → ℂ)} (hL : HEq L' L)
    (h0 : ∀ g x, X.e (ρ g x) = postOn M (L g) (X.e x)) : ∀ g x, X'.e (ρ' g x) = postOn M' (L' g) (X'.e x) := by
  subst hG
  obtain rfl := eq_of_heq hi
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : W' = W := by with_unfolding_all exact eq_of_heq hW
  subst W'
  rcases M with @⟨H, nacg, ips, σ, lam, ε, fr, enum, ds, fu, fg⟩
  rcases M' with @⟨H', nacg', ips', σ', lam', ε', fr', enum', ds', fu', fg'⟩
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have : H' = H := by with_unfolding_all exact eq_of_heq h1
  subst H'
  have : nacg' = nacg := by with_unfolding_all exact eq_of_heq h2
  subst nacg'
  have : ips' = ips := by with_unfolding_all exact eq_of_heq h3
  subst ips'
  have : σ' = σ := by with_unfolding_all exact eq_of_heq h4
  subst σ'
  have : lam' = lam := by with_unfolding_all exact eq_of_heq h5
  subst lam'
  have : ε' = ε := by with_unfolding_all exact eq_of_heq h6
  subst ε'
  have : fr' = fr := by with_unfolding_all exact eq_of_heq h7
  subst fr'
  have : X' = X := by with_unfolding_all exact eq_of_heq hX
  subst X'
  have : ρ' = ρ := by with_unfolding_all exact eq_of_heq hρ
  subst ρ'
  have : L' = L := by with_unfolding_all exact eq_of_heq hL
  subst L'
  exact (by with_unfolding_all exact (h0 :))

end Comparison₂

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}


private theorem actL_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {β : ∀ i, GL (Fin (Wc a.D i).rank) (Lev.EAf a.D)} {β' : ∀ i, GL (Fin (Wc a'.D i).rank) (Lev.EAf a'.D)} (hβ : HEq β' β)
    {Pg : Finset (Pl a.D.host.E)} {Pg' : Finset (Pl a'.D.host.E)} (hPg : HEq Pg' Pg)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {eG : G ≃* G0 Pg a.D.R.r} {eG' : G' ≃* G0 Pg' a'.D.R.r} (he : HEq eG' eG) :
    HEq (fun g => Links.actL _ (β' i') (LiftExt.datW i' Pg') (eG' g)) (fun g => Links.actL _ (β i) (LiftExt.datW i Pg) (eG g)) := by
  subst hG
  obtain rfl := eq_of_heq hi
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : i' = i := by with_unfolding_all exact Fin.ext h.symm
  subst i'
  have : β' = β := by with_unfolding_all exact eq_of_heq hβ
  subst β'
  have : Pg' = Pg := by with_unfolding_all exact eq_of_heq hPg
  subst Pg'
  have : eG' = eG := by with_unfolding_all exact eq_of_heq he
  subst eG'
  exact (by with_unfolding_all exact ((HEq.refl (fun g => Links.actL _ (β i) (LiftExt.datW i Pg) (eG g))) :))

private theorem meas_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {β : ∀ i, GL (Fin (Wc a.D i).rank) (Lev.EAf a.D)} {β' : ∀ i, GL (Fin (Wc a'.D i).rank) (Lev.EAf a'.D)} (hβ : HEq β' β)
    {Pg : Finset (Pl a.D.host.E)} {Pg' : Finset (Pl a'.D.host.E)} (hPg : HEq Pg' Pg)
    {ν : Measure (GA a.D (Wc a.D i))} {ν' : Measure (GA a'.D (Wc a'.D i'))} (hν : HEq ν' ν)
    {fd : Set (GA a.D (Wc a.D i))} {fd' : Set (GA a'.D (Wc a'.D i'))} (hfd : HEq fd' fd)
    (h0 : IsMeasFD (Wc a.D i) (lev a.D.sp.cm (Wc a.D i).gram (β i) (LiftExt.datW i Pg)) ν fd) :
    IsMeasFD (Wc a'.D i') (lev a'.D.sp.cm (Wc a'.D i').gram (β' i') (LiftExt.datW i' Pg')) ν' fd' := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : i' = i := by with_unfolding_all exact Fin.ext h.symm
  subst i'
  have : β' = β := by with_unfolding_all exact eq_of_heq hβ
  subst β'
  have : Pg' = Pg := by with_unfolding_all exact eq_of_heq hPg
  subst Pg'
  have : ν' = ν := by with_unfolding_all exact eq_of_heq hν
  subst ν'
  have : fd' = fd := by with_unfolding_all exact eq_of_heq hfd
  subst fd'
  exact (by with_unfolding_all exact (h0 :))

private theorem onb_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {BV : a.D.what₂.Tau → Matrix (Fin (Vc a.D i).rank) (Fin (Vc a.D i).rank) ℂ}
    {BV' : a'.D.what₂.Tau → Matrix (Fin (Vc a'.D i').rank) (Fin (Vc a'.D i').rank) ℂ} (hBV : HEq BV' BV)
    (h0 : ∀ τ, IsONBasis (gramAt a.D (Vc a.D i) τ) 1 (BV τ) (Vc a.D i).rank) :
    ∀ τ, IsONBasis (gramAt a'.D (Vc a'.D i') τ) 1 (BV' τ) (Vc a'.D i').rank := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : i' = i := by with_unfolding_all exact Fin.ext h.symm
  subst i'
  have : BV' = BV := by with_unfolding_all exact eq_of_heq hBV
  subst BV'
  exact (by with_unfolding_all exact (h0 :))

private theorem labE_heq (hP : B'.toPre = B.toPre) (ι : a.D.what₂.LL →+* a'.D.what₂.LL)
    (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x) (σ' : a'.D.what₂.LL →+* ℂ) :
    HEq (labE (D := a'.D) σ') (labE (D := a.D) (σ'.comp ι)) := by
  have e : labE (D := a.D) a.D.what₂.embLL = tauE a.D := funext fun τ => B.fields_embC τ
  have e' : labE (D := a'.D) a'.D.what₂.embLL = tauE a'.D := funext fun τ => B'.fields_embC τ
  unfold labE at *
  generalize labLL a'.D = l' at e' ⊢
  generalize labLL a.D = l at e ⊢
  generalize a'.D.what₂.embLL = j' at e' hι
  generalize a.D.what₂.embLL = j at e hι
  have ht : HEq (tauE a'.D) (tauE a.D) := by
    clear e e' hι
    rcases B' with ⟨P'⟩
    change P' = B.toPre at hP
    subst hP
    exact (by with_unfolding_all exact ((HEq.refl (tauE a.D)) :))
  rw [← e, ← e'] at ht
  clear e e'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have ht' := eq_of_heq ht
  refine heq_of_eq (funext fun τ => RingHom.ext fun x => ?_)
  exact congrArg σ' (j'.injective ((DFunLike.congr_fun (congrFun ht' τ) x).trans (hι _).symm))

private theorem dim_eq (hP : B'.toPre = B.toPre) {W : HSp a.D} {W' : HSp a'.D} (hW : HEq W' W) {σ : a.D.what₂.LL →+* ℂ}
    {σ' : a'.D.what₂.LL →+* ℂ} (hl : HEq (labE (D := a'.D) σ') (labE (D := a.D) σ)) :
    (∏ ρ, ((dimK _ _ (kapAt W' σ' ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ) := by
  unfold kapAt lab
  generalize labE (D := a'.D) σ' = l' at hl ⊢
  generalize labE (D := a.D) σ = l at hl ⊢
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : W' = W := by with_unfolding_all exact eq_of_heq hW
  subst W'
  have : l' = l := by with_unfolding_all exact eq_of_heq hl
  subst l'
  exact rfl

variable {G G' : Type} [iG : Group G] [Fintype G] [iG' : Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}

private theorem hw_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    (hθ : HEq R'.θ R.θ) (hβ : HEq R'.βW R.βW) (hPg : HEq R'.Pg R.Pg) (ι : a.D.what₂.LL →+* a'.D.what₂.LL)
    (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x) (σ' : a'.D.what₂.LL →+* ℂ)
    (hM : DSTie (R'.MW i' σ') (R.MW i (σ'.comp ι))) (hH : HEq (R'.HW i' σ') (R.HW i (σ'.comp ι)))
    (hν : HEq (R'.νW i') (R.νW i)) (hfd : HEq (R'.fdW i') (R.fdW i)) (h0 : R.models_HW) :
    (R'.HW i' σ').Is (R'.Wall i' σ') (Links.ipAt (R'.MW i' σ') (R'.νW i') (R'.fdW i')) := by
  have hW := wc_heq hP h
  have hl := lev_heq hP h hβ hPg
  have hd := dim_eq hP hW (labE_heq hP ι hι σ')
  have f0 : (R.HW i (σ'.comp ι)).Is (Mult R.θ _ (levS _ (R.βW i) (LiftExt.datW i R.Pg)) (levChi _ (R.βW i) (LiftExt.datW i R.Pg)))
      fun T T' => (∏ ρ, ((dimK _ _ (kapAt (Wc a.D i) (σ'.comp ι) ρ) : ℚ) : ℂ)) * ipM (R.MW i (σ'.comp ι)) (R.νW i) (R.fdW i) T T' := (by with_unfolding_all exact ((h0 i (σ'.comp ι)) :))
  rw [← hd] at f0
  have k := is_of hP hW hM hH (mult_heq hP hW hM hθ hl.1 hl.2) hν hfd _ f0
  exact (by with_unfolding_all exact (k :))

private theorem gw_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    (hG : G' = G) (hi : HEq iG' iG) (hβ : HEq R'.βW R.βW) (hPg : HEq R'.Pg R.Pg) (he : HEq R'.eG R.eG)
    {σ : a.D.what₂.LL →+* ℂ} {σ' : a'.D.what₂.LL →+* ℂ}
    (hM : DSTie (R'.MW i' σ') (R.MW i σ)) (hH : HEq (R'.HW i' σ') (R.HW i σ)) (hg : HEq (R'.gW i' σ') (R.gW i σ))
    (h0 : R.models_gW) :
    ∀ g x, (R'.HW i' σ').e (R'.gW i' σ' g x) =
      postOn _ (Links.actL (Wc a'.D i') (R'.βW i') (R'.datWp i' R'.triv) (R'.eG g)) ((R'.HW i' σ').e x) := by
  have hW := wc_heq hP h
  have f0 : ∀ g x, (R.HW i σ).e (R.gW i σ g x) =
      postOn _ ((fun g => Links.actL _ (R.βW i) (LiftExt.datW i R.Pg) (R.eG g)) g) ((R.HW i σ).e x) := (by with_unfolding_all exact ((h0 i σ) :))
  have k := act_of hP hW hM hH hG hi hg (actL_heq hP h hβ hPg hG hi he) f0
  exact (by with_unfolding_all exact (k :))

private theorem nu_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    (hβ : HEq R'.βW R.βW) (hPg : HEq R'.Pg R.Pg) (hν : HEq (R'.νW i') (R.νW i)) (hfd : HEq (R'.fdW i') (R.fdW i))
    (h0 : R.models_νW) :
    IsMeasFD (Wc a'.D i') (lev a'.D.sp.cm (Wc a'.D i').gram (R'.βW i') (R'.datWp i' R'.triv)) (R'.νW i') (R'.fdW i') := by
  have f0 : IsMeasFD (Wc a.D i) (lev a.D.sp.cm (Wc a.D i).gram (R.βW i) (LiftExt.datW i R.Pg)) (R.νW i) (R.fdW i) := (by with_unfolding_all exact ((h0 i) :))
  exact (by with_unfolding_all exact ((meas_of hP h hβ hPg hν hfd f0) :))

private theorem modW_of (hP : B'.toPre = B.toPre) (hG : G' = G) (hi : HEq iG' iG)
    (hθ : HEq R'.θ R.θ) (hβ : HEq R'.βW R.βW) (hPg : HEq R'.Pg R.Pg) (he : HEq R'.eG R.eG) (ι : a.D.what₂.LL →+* a'.D.what₂.LL)
    (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x)
    (H : ∀ (i : Fin a.D.R.m) (i' : Fin a'.D.R.m), (i : ℕ) = i' → HEq (R'.BV i') (R.BV i) ∧ HEq (R'.νW i') (R.νW i) ∧
      HEq (R'.fdW i') (R.fdW i) ∧ ∀ σ', DSTie (R'.MW i' σ') (R.MW i (σ'.comp ι)) ∧ HEq (R'.HW i' σ') (R.HW i (σ'.comp ι)) ∧
        HEq (R'.gW i' σ') (R.gW i (σ'.comp ι)))
    (h0 : R.IsModels) : ModW R' := by
  have hm := LiftExt.m_eq (a := a) (a' := a') hP
  refine ⟨fun i' σ' => ?_, fun i' σ' => ?_, fun i' => ?_, fun i' => ?_⟩
  all_goals
    have h : ((Fin.cast hm i' : Fin a.D.R.m) : ℕ) = i' := rfl
    generalize (Fin.cast hm i' : Fin a.D.R.m) = i at h
    obtain ⟨hBV, hν, hfd, h2⟩ := H i i' h
  · exact hw_of hP h hθ hβ hPg ι hι σ' (h2 σ').1 (h2 σ').2.1 hν hfd h0.HW
  · exact gw_of hP h hG hi hβ hPg he (h2 σ').1 (h2 σ').2.1 (h2 σ').2.2 h0.gW
  · exact nu_of hP h hβ hPg hν hfd h0.νW
  · exact onb_of hP h hBV (h0.BV i)

end Fields

end GlobalTheory.Mem.R3.Rw.ModWExt

end

open GlobalTheory.Mem.R3.Rw.ModWExt in

theorem _root_.GlobalTheory.T.modW_of_rSideW : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → ModW R'.toRealDat := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hpx hS
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hG := LiftExt.gc_eq hP hpx
  have hb := z.pins.char.base.models
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  clear_value ι
  obtain ⟨-, hθ, hβ, -, -, -, -, -, -, hPg, he, -, h1, -⟩ := hS
  refine modW_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP hG.1 hG.2 hθ hβ hPg he ι hι (fun i i' h => ?_) hb
  obtain ⟨-, -, -, -, -, -, hBV, -, -, -, -, -, -, -, -, -, hν, hfd, h2⟩ := h1 i i' h
  refine ⟨hBV, hν, hfd, fun σ' => ?_⟩
  obtain ⟨⟨m1, m2, m3, m4, m5, m6, m7, -⟩, hH, hg, -⟩ := (h2 ι hι).1 σ'
  exact ⟨⟨m1, m2, m3, m4, m5, m6, m7⟩, hH, hg⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormGroupsModelsActionsMeasuresBasesCharacterise =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBase =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBase", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCharactersExtendedDataEqMapSmallerData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.WeilExt



theorem idemSame_of_keep : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → GrpTrue Z.N f → GrpTrue Z'.N f' → RSideW z Wt' R' →
  ∀ cG : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd, Keep R'.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG → IdemSame z Xg := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hp hG hG' hR cG hK g' g hg
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -⟩ := hR
  have hB := hE.1
  cases B
  cases B'
  dsimp only at hB
  subst hB
  cases hf
  have hpx : w'.px = w.px := eq_of_heq hp
  cases w'
  dsimp only at hpx
  subst hpx
  cases hg
  obtain ⟨plg, iso, hpl, hid, -, hbc⟩ := z.pins.keep.grp
  obtain ⟨plg2, iso', hpl', hid', -, hbc'⟩ := hK.grp
  refine (hid' g).trans (Eq.trans ?_ (hid g).symm)
  refine Eq.trans ?_ (TypesTrue.typeIdempotent_coeff_across_layers hG hG' ((z.R.eG.trans z.cG) g))
  congr 1
  funext kv'
  obtain ⟨k, v'⟩ := kv'
  obtain ⟨v, rfl⟩ : ∃ v, v' = plEquiv Z.N.naut Z'.N.naut k v := ⟨_, (Equiv.apply_symm_apply _ v').symm⟩
  show _ = ((z.R.eG.trans z.cG) g) ⟨k, (plEquiv Z.N.naut Z'.N.naut k).symm (plEquiv Z.N.naut Z'.N.naut k v)⟩
  rw [Equiv.symm_apply_apply]
  have hP : R'.Pg = z.R.Pg := eq_of_heq hPg
  have hQ : (plg2 ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
    rw [hpl', hpl]
    exact TypesTrue.plGw_plEquiv hG hG' k v
  exact GlobalTheory.Mem.R3.DefLatBC.bc_eq_of_heq hP z.R.eG R'.eG heG g _ _ hQ (iso ⟨k, v⟩)
    (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) _ _ (hbc g ⟨k, v⟩) (hbc' g ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)

end GlobalTheory.Mem.R3.Rw.WeilExt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBase =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBaseStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBaseStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

theorem _root_.GlobalTheory.T.goodIdempotent_coefficients_agree_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → GrpTrue Z.N f → GrpTrue Z'.N f' → RSideW z Wt' R' →
  ∀ cG : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd, Keep R'.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG → IdemSame z Xg := by
  first | exact @GlobalTheory.Mem.R3.Rw.WeilExt.idemSame_of_keep
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBaseStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBaseStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBaseStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

theorem _root_.GlobalTheory.T.liftCharacters_agree_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  first | exact @GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBaseStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDefiniteFormsLargerFieldCombinationSmall =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDefiniteFormsLargerFieldCombinationSmall", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValues\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.JSpanPf

private theorem span_of_bc {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
    {S : Formalism.L2.Col.GSD K} {S' : Formalism.L2.Col.GSD L} (b : Formalism.L2.Col.GSDBC ι S S') {M M' : Type} [AddCommGroup M'] [Module L M']
    (r : S.EqFun → M) (r' : S'.EqFun ≃ₗ[L] M') (c : L →+* ℂ) {α α' U U' : Type} (n : NormedAddCommGroup U)
    (n' : NormedAddCommGroup U') (ip : InnerProductSpace ℂ U) (ip' : InnerProductSpace ℂ U') (hα : α' = α) (hU : U' = U)
    (hn : HEq n' n) (hip : HEq ip' ip) (j : M → α → U) (j' : M' →ₛₗ[c] (α' → U'))
    (h : ∀ φ, HEq (j' (r' (b.lift φ))) (j (r φ))) (x' : M') :
    ∃ (m : ℕ) (a : Fin m → L) (x : Fin m → M), HEq (j' x') (∑ k, c (a k) • j (x k)) := by
  subst hα hU
  cases hn
  cases hip
  obtain ⟨F⟩ := Formalism.L2.Col.CoefFrame.nonempty ι
  obtain ⟨φ', rfl⟩ := r'.surjective x'
  obtain ⟨m, a, g, hg⟩ := Submodule.mem_span_set'.1 (b.mem_span_lift F φ')
  choose ψ hψ using fun k => (g k).2
  refine ⟨m, a, fun k => r (ψ k), heq_of_eq ?_⟩

  rw [← hg, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, LinearMap.map_smulₛₗ, ← hψ k, eq_of_heq (h (ψ k))]



private theorem exists_bc {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl) (hE : Enl0 B B') (hf : HEq f' f) (hpx : HEq w'.px w.px)
    (k k' : ℕ) (hk : k' = k) (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x) :
    ∃ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 k)
      (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 k'),
      ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 k).EqFun) d d', HEq d' d →
        HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((b.lift ψ).1 d').1)
          (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (ψ.1 d).1) := by
  subst hk
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hv : (Base.primes (baseOfColW w') w'.px).vGs = (Base.primes (baseOfColW w) w.px).vGs := by
    rw [hpx']
    rfl
  have hφ' : ∀ x, (baseOfColW w').embLL (φ x) = (baseOfColW w).embLL x := hφ
  have hC : w'.I.C = w.I.C := w'.C_eq.trans ((eq_of_heq hf).trans w.C_eq.symm)
  refine GlobalTheory.Mem.R3.DefLatBC.gsdbc_round_reidx (baseOfColW w).fields φ (baseOfColW w').tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hφ
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hφ' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' _).trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w Wt).symm)
  · refine glue_inv_coefMap_of_empty φ (twistRamifiedPrimes_empty_colTuples w Wt) (twistRamifiedPrimes_empty_colTuples w' _) _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of φ p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    rw [hφ']
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    rw [hC] at e1
    exact e1.trans e2.symm



private theorem gf_eq {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} (Z : w.Lt) (Z' : w'.Lt) (h : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m)
    (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    (↥(Bridge.Gf (Vc (w'.st Z').toD7 i')) : Type) = ↥(Bridge.Gf (Vc (w.st Z).toD7 i)) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at h
  subst h
  have e0 : i = i' := Fin.ext hi
  subst e0
  rfl

end GlobalTheory.Mem.R3.Rw.JSpanPf


theorem _root_.GlobalTheory.T.rationalDefiniteForms_largerField_combination_smallerField : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → RSideW z Wt' R' → JSpan z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hRS i i' hii x'
  obtain ⟨ι, hι⟩ := exists_iota_comp B.embLL B'.embLL hE.2.2.2
  obtain ⟨b, hb⟩ := GlobalTheory.Mem.R3.Rw.JSpanPf.exists_bc w w' Wt Wt' hE hf hpx ((i : ℕ) + 1) ((i' : ℕ) + 1) (by rw [hii]) ι hι
  have hj := fun φ => hRS.2.2.2.2.2.2.2.2.2.2.2.2.2 i i' hii (Formalism.L2.Col.mtKOk _ _ _ _ hX _) (Formalism.L2.Col.mtKOk _ _ _ _ hX' _) φ
    (b.lift φ) (hb φ)
  have hc := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii
  have key := GlobalTheory.Mem.R3.Rw.JSpanPf.span_of_bc b
    (fun φ => (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk _ _ _ _ hX _) φ)
    ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk _ _ _ _ hX' _))
    B'.embLL (z.R.cV i).nW (R'.cV i').nW (z.R.cV i).iW (R'.cV i').iW (GlobalTheory.Mem.R3.Rw.JSpanPf.gf_eq Z Z' hE.1 i i' hii)
    (eq_of_heq hc.1) hc.2.2.1 hc.2.2.2.1
    (fun x => z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact (x :))))
    ((by with_unfolding_all exact (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) :))) ((by with_unfolding_all exact (hj :))) ((by with_unfolding_all exact (x' :)))
  exact (by with_unfolding_all exact (key :))
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDefiniteFormsLargerFieldCombinationSmall =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleHilbertModelDefiniteFormsEnlarged =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleHilbertModelDefiniteFormsEnlarged", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\nimport Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.ModVExt

section Generic

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

private theorem is_move (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ χ' : J →* ℂˣ) (e : χ' = χ)
    (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    {I I' : Type} [Fintype I] [Fintype I'] (y : I → G) (y' : I' → G) (hy : Bridge.IsReps ι J y) (hy' : Bridge.IsReps ι J y')
    (H : HMod (G → W)) (h : H.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y)) :
    H.Is (Bridge.AdForms ι ρ J χ') (Bridge.adInner ι J y') := by
  subst e
  refine ⟨h.1, h.2.1, fun x x' => ?_⟩
  rw [h.2.2]
  exact Bridge.adInnerIndep_holds ι ρ J χ' hρ hχ I I' y y' hy hy' _ (h.2.1 ▸ LinearMap.mem_range_self _ x) _
    (h.2.1 ▸ LinearMap.mem_range_self _ x')

private theorem norm_units_of_finite {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (u : H) : ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have hfin := Fintype.ofFinite H
  have h1 : (χ u) ^ (Fintype.card H) = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  have h2 : ‖((χ u : ℂˣ) : ℂ)‖ ^ (Fintype.card H) = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

end Generic

section Free

variable {D : D7}

private theorem norm_chi (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ‖((levEnv V β L).χ k : ℂ)‖ = 1 := by
  have hf : ∀ PP : Pl D.host.E, Finite (kP PP)ˣ := fun PP => Finite.of_injective _ Units.val_injective
  show ‖((levFn β (flag1L L) (Formalism.UG.bc (swapAE D) k.1.1) : ℂˣ) : ℂ)‖ = 1
  generalize Formalism.UG.bc (swapAE D) k.1.1 = x
  unfold levFn
  simp only [Units.val_mul, norm_mul, Units.coe_prod, norm_prod]
  rw [show ext1 (flag1L L).P.H (flag1L L).P.chi (rTup β (flag1L L) x) = 1 from subgroupCharExtension_one_apply _ _]
  simp [norm_units_of_finite]

private def datC (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  datY _ D.R.r D.R.t 1 hr Pg Q (LevelP.triv _ _ _) (fun _ => chi) xi Frm.A

private def MV (V : HSp D) (c : CoefA V) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    {I : Type} [Fintype I] (y : I → Bridge.Gf V) (H : HMod (Bridge.Gf V → c.W)) (ν : Measure (GA D V)) (fd : Set (GA D V)) : Prop :=
  H.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y) ∧
  IsMeasDef V (lev D.sp.cm V.gram β L) ν fd

private def RP (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    {I : Type} (y : I → Bridge.Gf V) : Prop := Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y

private theorem mv_move (V : HSp D) (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (hr : D.R.r ≤ V.rank)
    (Pg : Finset (Pl D.host.E)) (chi xi chi' xi' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (hchi : ∀ PP ∈ Pg, chi' PP = chi PP)
    {I I' : Type} [Fintype I] [Fintype I'] (y : I → Bridge.Gf V) (y' : I' → Bridge.Gf V)
    (hy : RP V β (datC V hr Pg ∅ chi xi) y) (hy' : RP V β (datC V hr Pg ∅ chi' xi') y')
    (H : HMod (Bridge.Gf V → c.W)) (ν : Measure (GA D V)) (fd : Set (GA D V))
    (h : MV V c β (datC V hr Pg ∅ chi xi) y H ν fd) : MV V c β (datC V hr Pg ∅ chi' xi') y' H ν fd := by
  refine ⟨?_, h.2⟩
  refine is_move (Bridge.ratF V) c.coef.ρ (levEnv V β (datC V hr Pg ∅ chi xi)).J _ (levEnv V β (datC V hr Pg ∅ chi' xi')).χ ?_
    (fun γ => hc.2.1 γ.1) (norm_chi V β _) y y' hy hy' H h.1
  ext1 k
  show levFn β (flag1L (datC V hr Pg ∅ chi' xi')) (Formalism.UG.bc (swapAE D) k.1.1) =
    levFn β (flag1L (datC V hr Pg ∅ chi xi)) (Formalism.UG.bc (swapAE D) k.1.1)
  generalize Formalism.UG.bc (swapAE D) k.1.1 = x
  unfold levFn
  congr 1
  congr 1
  refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => ?_
  show (chi' PP)⁻¹ _ = (chi PP)⁻¹ _
  rw [hchi PP hP]
  rfl

end Free

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

private theorem mv_of (hP : B'.toPre = B.toPre) {V : HSp a.D} {V' : HSp a'.D} (hV : HEq V' V) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf a.D)} {β' : GL (Fin V'.rank) (Lev.EAf a'.D)} (hβ : HEq β' β)
    (hr : a.D.R.r ≤ V.rank) (hr' : a'.D.R.r ≤ V'.rank)
    {Pg Q : Finset (Pl a.D.host.E)} {Pg' Q' : Finset (Pl a'.D.host.E)} (hPg : HEq Pg' Pg) (hQ : Q = ∅) (hQ' : Q' = ∅)
    {chi xi : ∀ PP : Pl a.D.host.E, (kP PP)ˣ →* ℂˣ} {chi' xi' : ∀ PP : Pl a'.D.host.E, (kP PP)ˣ →* ℂˣ}
    (hchi : ∀ PP' PP, HEq PP' PP → PP ∈ Pg → HEq (chi' PP') (chi PP))
    {I I' : Type} [Fintype I] [Fintype I'] {y : I → Bridge.Gf V} {y' : I' → Bridge.Gf V'}
    (hy : RP V β (datC V hr Pg Q chi xi) y) (hy' : RP V' β' (datC V' hr' Pg' Q' chi' xi') y')
    {H H'} (hH : HEq H' H) {ν ν'} (hν : HEq ν' ν) {fd fd'} (hfd : HEq fd' fd)
    (h0 : MV V c β (datC V hr Pg Q chi xi) y H ν fd) : MV V' c' β' (datC V' hr' Pg' Q' chi' xi') y' H' ν' fd' := by
  subst hQ hQ'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ( (
  have e : @Eq (type_of% (W₁)) ((by with_unfolding_all exact ((c.W) :))) (W₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W₁)) (W₁) (((c.W))) (((c1)))).symm : _))
  clear (c1)
  subst e))
  ( (
  have e : @Eq (type_of% (nW')) ((by with_unfolding_all exact ((c.nW) :))) (nW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nW')) (nW') (((c.nW))) (((c3)))).symm : _))
  clear (c3)
  subst e))
  ( (
  have e : @Eq (type_of% (iW')) ((by with_unfolding_all exact ((c.iW) :))) (iW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (iW')) (iW') (((c.iW))) (((c4)))).symm : _))
  clear (c4)
  subst e))
  ( (
  have e : @Eq (type_of% (ρ₁)) ((by with_unfolding_all exact ((c.ρ) :))) (ρ₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ρ₁)) (ρ₁) (((c.ρ))) (((c2)))).symm : _))
  clear (c2)
  subst e))
  ( (
  have e : @Eq (type_of% (β')) ((by with_unfolding_all exact ((β) :))) (β') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (β')) (β') (((β))) (((hβ)))).symm : _))
  clear (hβ)
  subst e))
  ( (
  have e : @Eq (type_of% (Pg')) ((by with_unfolding_all exact ((Pg) :))) (Pg') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Pg')) (Pg') (((Pg))) (((hPg)))).symm : _))
  clear (hPg)
  subst e))
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((H))) (((hH)))).symm : _))
  clear (hH)
  subst e))
  ( (
  have e : @Eq (type_of% (ν')) ((by with_unfolding_all exact ((ν) :))) (ν') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ν')) (ν') (((ν))) (((hν)))).symm : _))
  clear (hν)
  subst e))
  ( (
  have e : @Eq (type_of% (fd')) ((by with_unfolding_all exact ((fd) :))) (fd') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (fd')) (fd') (((fd))) (((hfd)))).symm : _))
  clear (hfd)
  subst e))
  have e : ∀ PP : Pl a.D.host.E, PP ∈ Pg → HEq (chi' ((by with_unfolding_all exact (PP :)))) (chi PP) :=
    fun PP hm => hchi ((by with_unfolding_all exact (PP :))) PP ((by with_unfolding_all exact ((HEq.refl PP) :))) hm
  exact (by with_unfolding_all exact ((mv_move V c hc β hr Pg chi xi ((by with_unfolding_all exact (chi' :))) ((by with_unfolding_all exact (xi' :))) (fun PP hm => eq_of_heq ((by with_unfolding_all exact ((e PP hm) :)))) y (I' := I') ((by with_unfolding_all exact (y' :))) hy ((by with_unfolding_all exact (hy' :))) H ν fd h0) :))

private theorem beta_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {β : ∀ i, GL (Fin (Vc a.D i).rank) (Lev.EAf a.D)} {β' : ∀ i, GL (Fin (Vc a'.D i).rank) (Lev.EAf a'.D)} (hβ : HEq β' β) :
    HEq (β' i') (β i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((Fin.ext h : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i') :))
  clear h
  subst e
  ( (
  have e : @Eq (type_of% (β')) ((by with_unfolding_all exact ((β) :))) (β') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (β')) (β') (((β))) (((hβ)))).symm : _))
  clear (hβ)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl (β i)) :))

variable {G G' : Type} [iG : Group G] [Fintype G] [iG' : Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}

private theorem modV_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (hβ : HEq R'.βV R.βV) (hPg : HEq R'.Pg R.Pg) (hQ : R.Q t = ∅) (hQ' : R'.Q t' = ∅)
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW)
    (hchi : ∀ PP' PP, HEq PP' PP → PP ∈ R.Pg → HEq (R'.chi ((i' : ℕ) + 1) PP') (R.chi ((i : ℕ) + 1) PP))
    (hHV : HEq (R'.HV i' t') (R.HV i t)) (hν : HEq (R'.νV i' t') (R.νV i t)) (hfd : HEq (R'.fdV i' t') (R.fdV i t))
    (hm : R.IsModels) :
    (R'.HV i' t').Is (Bridge.AdForms (Bridge.ratF (Vc a'.D i')) (R'.cV i').coef.ρ (levEnv _ (R'.βV i') (R'.datVt i' t')).J
      (levEnv _ (R'.βV i') (R'.datVt i' t')).χ)
    (Bridge.adInner (Bridge.ratF (Vc a'.D i')) (levEnv _ (R'.βV i') (R'.datVt i' t')).J (R'.B.L i' t').pres.y) ∧
  IsMeasDef (Vc a'.D i') (lev a'.D.sp.cm (Vc a'.D i').gram (R'.βV i') (R'.datVt i' t')) (R'.νV i' t') (R'.fdV i' t') :=
  mv_of hP (LiftExt.vc_heq hP h) c1 c2 c3 c4 (hm.cV i) (beta_heq hP h hβ) (r_le_V i) (r_le_V i') hPg hQ hQ' hchi
    (xi := R.xiR t) (xi' := R'.xiR t') (y := (R.B.L i t).pres.y) (y' := (R'.B.L i' t').pres.y)
    (R.B.L i t).pres.reps (R'.B.L i' t').pres.reps hHV hν hfd ⟨hm.HV i t, hm.νV i t⟩

end Comparison₂

end GlobalTheory.Mem.R3.Rw.ModVExt

end


theorem _root_.GlobalTheory.T.referenceTuple_hilbertModel_definiteForms_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → R'.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 → RSide z Wt' R' → LevSame z Wt' R' → ModVAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE _ hS hL i'
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  obtain ⟨⟨-, -, -, -, -, -, hβ, -, -, hPg, -, -, h1, -⟩, h2⟩ := hS
  obtain ⟨c1, c2, c3, c4, -⟩ := h1 i i' h
  obtain ⟨-, -, hHV, -, -, hν, hfd⟩ := h2 i i' h
  exact ModVExt.modV_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h hβ hPg hL.2.2.2 hL.2.2.1 c1 c2 c3 c4
    (hL.1 i i' h).2 hHV hν hfd z.pins.char.base.models
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleHilbertModelDefiniteFormsEnlarged =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.RatExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Mem.R3.Rw.LiftExt

private theorem comb_gen {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] (Y : HMod E) (X : HMod E')
    (g : Y.H →ₗ[ℂ] X.H) (hinj : Function.Injective Y.e) (v : Y.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g v := by
  have e : v = ∑ k, s k • u k := hinj (by rw [eq_of_heq hv, map_sum]; simp only [map_smul])

  rw [e, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, eq_of_heq (hp k)]

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {V W : HSp a.D} {V' W' : HSp a'.D} {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}

private theorem comb_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W) (h : DSTie M' M) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW)
    {Y : HMod (Bridge.Gf V → c.W)} {Y' : HMod (Bridge.Gf V' → c'.W)} (hY : HEq Y' Y)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X) {g : Y.H →ₗ[ℂ] X.H} {g' : Y'.H →ₗ[ℂ] X'.H} (hg : HEq g' g)
    (hinj : Function.Injective Y.e) (v : Y'.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y'.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X'.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g' v := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (W')) ((by with_unfolding_all exact ((W) :))) (W') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W')) (W') (((W))) (((hW)))).symm : _))
  clear (hW)
  subst e))
  obtain ⟨H', s', l', ε', f', _, _, _, _⟩ := M'
  rename_i n' i' _ _ _ _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((M.H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((M.H))) (((h1)))).symm : _))
  clear (h1)
  subst e))
  ( (
  have e : @Eq (type_of% (n')) ((by with_unfolding_all exact ((M.nacg) :))) (n') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (n')) (n') (((M.nacg))) (((h2)))).symm : _))
  clear (h2)
  subst e))
  ( (
  have e : @Eq (type_of% (i')) ((by with_unfolding_all exact ((M.ips) :))) (i') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (i')) (i') (((M.ips))) (((h3)))).symm : _))
  clear (h3)
  subst e))
  ( (
  have e : @Eq (type_of% (s')) ((by with_unfolding_all exact ((M.σ) :))) (s') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (s')) (s') (((M.σ))) (((h4)))).symm : _))
  clear (h4)
  subst e))
  ( (
  have e : @Eq (type_of% (l')) ((by with_unfolding_all exact ((M.lam) :))) (l') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (l')) (l') (((M.lam))) (((h5)))).symm : _))
  clear (h5)
  subst e))
  ( (
  have e : @Eq (type_of% (ε')) ((by with_unfolding_all exact ((M.ε) :))) (ε') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ε')) (ε') (((M.ε))) (((h6)))).symm : _))
  clear (h6)
  subst e))
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((M.fr) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((M.fr))) (((h7)))).symm : _))
  clear (h7)
  subst e))
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ( (
  have e : @Eq (type_of% (W₁)) ((by with_unfolding_all exact ((c.W) :))) (W₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W₁)) (W₁) (((c.W))) (((c1)))).symm : _))
  clear (c1)
  subst e))
  ( (
  have e : @Eq (type_of% (nW')) ((by with_unfolding_all exact ((c.nW) :))) (nW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nW')) (nW') (((c.nW))) (((c3)))).symm : _))
  clear (c3)
  subst e))
  ( (
  have e : @Eq (type_of% (iW')) ((by with_unfolding_all exact ((c.iW) :))) (iW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (iW')) (iW') (((c.iW))) (((c4)))).symm : _))
  clear (c4)
  subst e))
  ( (
  have e : @Eq (type_of% (ρ₁)) ((by with_unfolding_all exact ((c.ρ) :))) (ρ₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ρ₁)) (ρ₁) (((c.ρ))) (((c2)))).symm : _))
  clear (c2)
  subst e))
  ( (
  have e : @Eq (type_of% (Y')) ((by with_unfolding_all exact ((Y) :))) (Y') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Y')) (Y') (((Y))) (((hY)))).symm : _))
  clear (hY)
  subst e))
  ( (
  have e : @Eq (type_of% (X')) ((by with_unfolding_all exact ((X) :))) (X') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (X')) (X') (((X))) (((hX)))).symm : _))
  clear (hX)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  exact (by with_unfolding_all exact ((comb_gen Y X g hinj ((v)) s u ((hv)) ((p)) ((hp))) : _))

end Comparison₂

private theorem apply_eq {m m' : ℕ} (hm : m' = m) {F : Fin m → ℕ} {F' : Fin m' → ℕ} (hF : HEq F' F) {i : Fin m} {i' : Fin m'}
    (h : (i : ℕ) = i') : F i = F' i' := by
  subst hm
  obtain rfl := eq_of_heq hF
  obtain rfl : i = i' := Fin.ext h
  rfl

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}



private theorem rat_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW)
    (hM : DSTie (R'.MW i' a'.D.what₂.embLL) (R.MW i a.D.what₂.embLL)) (hHW : HEq (R'.HW i' a'.D.what₂.embLL) (R.HW i a.D.what₂.embLL))
    (hHV : HEq (R'.HV i' t') (R.HV i t)) (hg : HEq (R'.thG i' t') (R.thG i t)) (hn : HEq R'.nW R.nW)
    (ι : a.D.what₂.LL →+* a'.D.what₂.LL) (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x)
    (hj : ∀ (σ' : a'.D.what₂.LL →+* ℂ) x x', CrdOver ι x x' → HEq ((R'.FW i').j σ' x') ((R.FW i).j (σ'.comp ι) x))
    (hinj : Function.Injective (R.HV i t).e) (hjV : ∀ x, (R.HV i t).e (R.jV i t x) = R.B.jL i t x) (hr : RatAt R t)
    (x' : A'.fam.amb.FL i' t') {n : ℕ} (b : Fin n → a'.D.what₂.LL) (x : Fin n → A.fam.amb.FL i t)
    (hx : HEq (R'.B.jL i' t' x') (∑ k, a'.D.what₂.embLL (b k) • R.B.jL i t (x k)))
    (v : (R'.HV i' t').H) (hv : (R'.HV i' t').e v = R'.B.jL i' t' x') :
    ∃ y, (R'.FW i').j (sg0 a'.D A') y = R'.thG i' t' v := by
  have s : a.D.what₂.embLL = sg0 a.D A := (sgAt_mk _ R.hv0).symm
  have s' : a'.D.what₂.embLL = sg0 a'.D A' := (sgAt_mk _ R'.hv0).symm
  have hM0 : DSTie (R'.MW i' (sg0 a'.D A')) (R.MW i (sg0 a.D A)) := s ▸ s' ▸ hM
  have hHW0 : HEq (R'.HW i' (sg0 a'.D A')) (R.HW i (sg0 a.D A)) := s ▸ s' ▸ hHW
  have hc : (sg0 a'.D A').comp ι = sg0 a.D A := by
    rw [← s, ← s']; exact RingHom.ext hι
  have hmv : ∀ (σ₁ σ₂ : a.D.what₂.LL →+* ℂ), σ₁ = σ₂ → ∀ y, HEq ((R.FW i).j σ₁ y) ((R.FW i).j σ₂ y) := by
    intro σ₁ σ₂ e y; subst e; exact HEq.rfl
  have hn0 : R.nW i = R'.nW i' := apply_eq (LiftExt.m_eq hP) hn h
  choose y hy using fun k => hr i (x k) (R.jV i t (x k)) (hjV (x k))
  refine ⟨∑ k, b k • GeoFW.crdMap ι hn0 (y k), ?_⟩
  refine ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => LinearMap.map_smulₛₗ _ _ _)).trans ?_
  refine comb_of hP (vc_heq hP h) (wc_heq hP h) hM0 c1 c2 c3 c4 hHV hHW0 hg hinj v (fun k => sg0 a'.D A' (b k))
    (fun k => R.jV i t (x k)) ?_ (fun k => (R'.FW i').j (sg0 a'.D A') (GeoFW.crdMap ι hn0 (y k))) fun k => ?_
  · refine (heq_of_eq hv).trans (hx.trans (heq_of_eq ?_))
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (by with_unfolding_all exact ((congrArg₂ (fun (c : ℂ) (q : Bridge.Gf (Vc a.D i) → (R.cV i).W) => c • q) (DFunLike.congr_fun s' (b k)) (hjV (x k)).symm) :))
  · exact ((hj _ _ _ (GeoFW.crdOver_crdMap ι hn0 (y k))).trans (hmv _ _ hc _)).trans (heq_of_eq (hy k))

end Fields

end GlobalTheory.Mem.R3.Rw.RatExt


theorem _root_.GlobalTheory.T.referenceTuple_rationalForm_lifts_algebraic_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSide z Wt' R' → JSpan z Wt' R' → RatAt z.R.toRealDat (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) → RatAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hS hJ hr i' x' v hv
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  obtain ⟨⟨-, -, -, -, -, hn, -, -, -, -, -, -, h1, -⟩, h2⟩ := hS
  obtain ⟨c1, c2, c3, c4, -, -, -, m1, m2, m3, m4, m5, m6, m7, -, hHW, -, -, hWι⟩ := h1 i i' h
  obtain ⟨-, -, hHV, -, hg, -, -⟩ := h2 i i' h
  obtain ⟨n, b, x, hx⟩ := hJ i i' h x'
  have hb := z.pins.char.base.models
  exact RatExt.rat_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h c1 c2 c3 c4
    ⟨m1, m2, m3, m4, m5, m6, m7⟩ hHW hHV hg hn ι hι (fun σ' => ((hWι ι hι).1 σ').2.2.2) (hb.HV i _).1 (hb.jV i _) hr x' b x hx v hv
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleWeilDatumVectorPolynomialMapEnlarg =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleWeilDatumVectorPolynomialMapEnlarg", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.WeilAtExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.WeilFull GlobalTheory.Mem.R3.Rw.LiftExt


section Leaves

variable {B B' : Base} {C : Cols B} {C' : Cols B'} (a : Late B C) (a' : Late B' C')

private theorem thetaFun_heq (hP : B'.toPre = B.toPre) : HEq (@IsThetaFunO a'.D) (@IsThetaFunO a.D) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have e : @Eq (type_of% (@IsThetaFunO a.D)) ((by with_unfolding_all exact ((@IsThetaFunO a'.D) :))) (@IsThetaFunO a.D) := by
    funext ψ S T f
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · have h' : @IsThetaFunO a'.D ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) := (by with_unfolding_all exact (h :))
      exact ⟨(by with_unfolding_all exact (h'.quasi :)), (by with_unfolding_all exact (h'.level :)), (by with_unfolding_all exact (h'.cont :)), (by with_unfolding_all exact (h'.smooth :))⟩
    · have h' : @IsThetaFunO a'.D ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) := ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
      exact (by with_unfolding_all exact (h' :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

private theorem vacuum_heq (hP : B'.toPre = B.toPre) : HEq (@IsVacuum a'.D) (@IsVacuum a.D) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have e : @Eq (type_of% (@IsVacuum a.D)) ((by with_unfolding_all exact ((@IsVacuum a'.D) :))) (@IsVacuum a.D) := by
    funext m n x1 x2 x3 x4 x5 x6 x7
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · have h' : @IsVacuum a'.D m n ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) := (by with_unfolding_all exact (h :))
      exact ⟨(by with_unfolding_all exact (h'.inf :)), (by with_unfolding_all exact (h'.theta :)), (by with_unfolding_all exact (h'.lat :)), (by with_unfolding_all exact (h'.fock :)), (by with_unfolding_all exact (h'.norm :))⟩
    · have h' : @IsVacuum a'.D m n ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) :=
        ⟨(by with_unfolding_all exact (h.inf :)), (by with_unfolding_all exact (h.theta :)), (by with_unfolding_all exact (h.lat :)), (by with_unfolding_all exact (h.fock :)), (by with_unfolding_all exact (h.norm :))⟩
      exact (by with_unfolding_all exact (h' :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

private theorem placeModel_heq (hP : B'.toPre = B.toPre) : HEq (@IsPlaceModel a'.D) (@IsPlaceModel a.D) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have e : @Eq (type_of% (@IsPlaceModel a.D)) ((by with_unfolding_all exact ((@IsPlaceModel a'.D) :))) (@IsPlaceModel a.D) := by
    funext m n x1 x2 x3 x4 x5 x6 x7 x8
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · have h' : @IsPlaceModel a'.D m n ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) ((by with_unfolding_all exact (x8 :))) := (by with_unfolding_all exact (h :))
      exact ⟨(by with_unfolding_all exact (h'.trans :)), (by with_unfolding_all exact (h'.modul :)), (by with_unfolding_all exact (h'.vac :))⟩
    · have h' : @IsPlaceModel a'.D m n ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) ((by with_unfolding_all exact (x8 :))) :=
        ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
      exact (by with_unfolding_all exact (h' :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

private theorem pairSetup_heq (hP : B'.toPre = B.toPre) : HEq (@Fock.Sk.PairSetup a'.D) (@Fock.Sk.PairSetup a.D) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have e : @Eq (type_of% (@Fock.Sk.PairSetup a.D)) ((by with_unfolding_all exact ((@Fock.Sk.PairSetup a'.D) :))) (@Fock.Sk.PairSetup a.D) := by
    funext x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · have h' : @Fock.Sk.PairSetup a'.D ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) ((by with_unfolding_all exact (x8 :))) ((by with_unfolding_all exact (x9 :))) ((by with_unfolding_all exact (x10 :))) := (by with_unfolding_all exact (h :))
      exact ⟨(by with_unfolding_all exact (h'.std :)), (by with_unfolding_all exact (h'.inf :)), (by with_unfolding_all exact (h'.cartS :)), (by with_unfolding_all exact (h'.cartT :)), (by with_unfolding_all exact (h'.onbS :)), (by with_unfolding_all exact (h'.onbT :))⟩
    · have h' : @Fock.Sk.PairSetup a'.D ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (x3 :))) ((by with_unfolding_all exact (x4 :))) ((by with_unfolding_all exact (x5 :))) ((by with_unfolding_all exact (x6 :))) ((by with_unfolding_all exact (x7 :))) ((by with_unfolding_all exact (x8 :))) ((by with_unfolding_all exact (x9 :))) ((by with_unfolding_all exact (x10 :))) :=
        ⟨(by with_unfolding_all exact (h.std :)), (by with_unfolding_all exact (h.inf :)), (by with_unfolding_all exact (h.cartS :)), (by with_unfolding_all exact (h.cartT :)), (by with_unfolding_all exact (h.onbS :)), (by with_unfolding_all exact (h.onbT :))⟩
      exact (by with_unfolding_all exact (h' :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

end Leaves

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {V W : HSp a.D} {V' W' : HSp a'.D}

private theorem weilFull_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W)
    {ψ : AddChar (AF a.D.host.F) ℂ} {ψ' : AddChar (AF a'.D.host.F) ℂ} (hψ : HEq ψ' ψ)
    {μ η : (AE a.D)ˣ →* Circle} {μ' η' : (AE a'.D)ˣ →* Circle} (hμ : HEq μ' μ) (hη : HEq η' η)
    {ω ω'} (hω : HEq ω' ω) (h : IsWeilFull ψ V W μ (μ * η⁻¹) ω) : IsWeilFull ψ' V' W' μ' (μ' * η'⁻¹) ω' := by
  have k1 := thetaFun_heq a a' hP
  have k2 := pairSetup_heq a a' hP
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : V' = V := by with_unfolding_all exact eq_of_heq hV
  subst V'
  have : W' = W := by with_unfolding_all exact eq_of_heq hW
  subst W'
  have : ψ' = ψ := by with_unfolding_all exact eq_of_heq hψ
  subst ψ'
  have : μ' = μ := by with_unfolding_all exact eq_of_heq hμ
  subst μ'
  have : η' = η := by with_unfolding_all exact eq_of_heq hη
  subst η'
  have : ω' = ω := by with_unfolding_all exact eq_of_heq hω
  subst ω'
  have e1 : @Eq (type_of% (@IsThetaFunO a'.D)) (@IsThetaFunO a'.D) ((by with_unfolding_all exact (@IsThetaFunO a.D :))) := by
    with_unfolding_all exact (eq_of_heq k1 : _)
  have e2 : @Eq (type_of% (@Fock.Sk.PairSetup a'.D)) (@Fock.Sk.PairSetup a'.D) ((by with_unfolding_all exact (@Fock.Sk.PairSetup a.D :))) := by
    with_unfolding_all exact (eq_of_heq k2 : _)
  refine ⟨⟨(by with_unfolding_all exact (h.datum.std :)), (by with_unfolding_all exact (h.datum.hecS :)), (by with_unfolding_all exact (h.datum.hecT :)), (by with_unfolding_all exact (h.datum.resS :)), (by with_unfolding_all exact (h.datum.resT :)), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_pres :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_heis :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_aut :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_cont :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_unit :))
  · rewrite [e1]; exact (by with_unfolding_all exact (h.datum.om_split :))
  · delta SphInertAtO; rewrite [e1]; exact (by with_unfolding_all exact (h.inert :))
  · delta RealAtO; rewrite [e2, e1]; exact (by with_unfolding_all exact (h.real :))

private theorem thPVec_empty {D : D7} {ψ θ} {S T : HSp D} {sS sT ΛS ΛT βS βT Pg ξ} (ξ') {f₀ f}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ f₀ f) : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ' f₀ f := by
  have e : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP),
      omegaQ ∅ T.rank ξ' (-1) y = omegaQ ∅ T.rank ξ (-1) y := fun y => by simp [omegaQ]
  unfold IsThPVecOf at h ⊢
  simpa only [e] using h

private theorem thPVec_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W)
    {ψ : AddChar (AF a.D.host.F) ℂ} {ψ' : AddChar (AF a'.D.host.F) ℂ} (hψ : HEq ψ' ψ)
    {θ : InfFam a.D} {θ' : InfFam a'.D} (hθ : HEq θ' θ) {s s'} (hs : HEq s' s)
    {ΛV : Submodule (𝓞 a.D.host.E) (Fin V.rank → a.D.host.E)} {ΛV' : Submodule (𝓞 a'.D.host.E) (Fin V'.rank → a'.D.host.E)}
    (hΛV : HEq ΛV' ΛV)
    {ΛW : Submodule (𝓞 a.D.host.E) (Fin W.rank → a.D.host.E)} {ΛW' : Submodule (𝓞 a'.D.host.E) (Fin W'.rank → a'.D.host.E)}
    (hΛW : HEq ΛW' ΛW) {βV βV'} (hβV : HEq βV' βV) {βW βW'} (hβW : HEq βW' βW) {Pg Pg'} (hPg : HEq Pg' Pg)
    {f₀ f₀'} (h₀ : HEq f₀' f₀) {f f'} (hf : HEq f' f)
    (h : IsThPVecOf ψ θ V W (fun _ => 1) s ΛV ΛW βV βW Pg ∅ (fun _ => 1) f₀ f) :
    IsThPVecOf ψ' θ' V' W' (fun _ => 1) s' ΛV' ΛW' βV' βW' Pg' ∅ (fun _ => 1) f₀' f' := by
  have k1 := thetaFun_heq a a' hP
  have k2 := vacuum_heq a a' hP
  have k3 := placeModel_heq a a' hP
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : V' = V := by with_unfolding_all exact eq_of_heq hV
  subst V'
  have : W' = W := by with_unfolding_all exact eq_of_heq hW
  subst W'
  have : ψ' = ψ := by with_unfolding_all exact eq_of_heq hψ
  subst ψ'
  have : θ' = θ := by with_unfolding_all exact eq_of_heq hθ
  subst θ'
  have : s' = s := by with_unfolding_all exact eq_of_heq hs
  subst s'
  have : ΛV' = ΛV := by with_unfolding_all exact eq_of_heq hΛV
  subst ΛV'
  have : ΛW' = ΛW := by with_unfolding_all exact eq_of_heq hΛW
  subst ΛW'
  have : βV' = βV := by with_unfolding_all exact eq_of_heq hβV
  subst βV'
  have : βW' = βW := by with_unfolding_all exact eq_of_heq hβW
  subst βW'
  have : Pg' = Pg := by with_unfolding_all exact eq_of_heq hPg
  subst Pg'
  have : f₀' = f₀ := by with_unfolding_all exact eq_of_heq h₀
  subst f₀'
  have : f' = f := by with_unfolding_all exact eq_of_heq hf
  subst f'
  have e1 : @Eq (type_of% (@IsThetaFunO a'.D)) (@IsThetaFunO a'.D) ((by with_unfolding_all exact (@IsThetaFunO a.D :))) := by
    with_unfolding_all exact (eq_of_heq k1 : _)
  have e2 : @Eq (type_of% (@IsVacuum a'.D)) (@IsVacuum a'.D) ((by with_unfolding_all exact (@IsVacuum a.D :))) := by
    with_unfolding_all exact (eq_of_heq k2 : _)
  have e3 : @Eq (type_of% (@IsPlaceModel a'.D)) (@IsPlaceModel a'.D) ((by with_unfolding_all exact (@IsPlaceModel a.D :))) := by
    with_unfolding_all exact (eq_of_heq k3 : _)
  delta IsThPVecOf IsVacO IsThetaAt
  rewrite [e1, e2, e3]
  exact (by with_unfolding_all exact (h :))

variable {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}


private theorem cart_heq (hP : B'.toPre = B.toPre) (hW : HEq W' W) (h : DSTie M' M) : HEq (cart M') (cart M) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : W' = W := by with_unfolding_all exact eq_of_heq hW
  subst W'
  rcases M with @⟨H, nacg, ips, σ, lam, ε, fr, enum, ds, fu, fg⟩
  rcases M' with @⟨H', nacg', ips', σ', lam', ε', fr', enum', ds', fu', fg'⟩
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have : H' = H := by with_unfolding_all exact eq_of_heq h1
  subst H'
  have : nacg' = nacg := by with_unfolding_all exact eq_of_heq h2
  subst nacg'
  have : ips' = ips := by with_unfolding_all exact eq_of_heq h3
  subst ips'
  have : σ' = σ := by with_unfolding_all exact eq_of_heq h4
  subst σ'
  have : lam' = lam := by with_unfolding_all exact eq_of_heq h5
  subst lam'
  have : ε' = ε := by with_unfolding_all exact eq_of_heq h6
  subst ε'
  have : fr' = fr := by with_unfolding_all exact eq_of_heq h7
  subst fr'
  with_unfolding_all rfl

private theorem ioW_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W) (h : DSTie M' M)
    {θ : InfFam a.D} {θ' : InfFam a'.D} (hθ : HEq θ' θ)
    {ψ : AddChar (AF a.D.host.F) ℂ} {ψ' : AddChar (AF a'.D.host.F) ℂ} (hψ : HEq ψ' ψ) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW)
    {BV BV'} (hBV : HEq BV' BV) {io io'} (hio : HEq io' io) {ω ω'} (hω : HEq ω' ω) {v v'} (hv : HEq v' v) {Δ Δ'} (hΔ : HEq Δ' Δ)
    (h0 : IsIoW θ M c ω (pureTensorO ψ θ V W (fun _ => 1) (cart M) BV (onb M) v) Δ io) :
    IsIoW θ' M' c' ω' (pureTensorO ψ' θ' V' W' (fun _ => 1) (cart M') BV' (onb M') v') Δ' io' := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have : W' = W := by with_unfolding_all exact eq_of_heq hW
  subst W'
  rcases M with @⟨H, nacg, ips, σ, lam, ε, fr, enum, ds, fu, fg⟩
  rcases M' with @⟨H', nacg', ips', σ', lam', ε', fr', enum', ds', fu', fg'⟩
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have : H' = H := by with_unfolding_all exact eq_of_heq h1
  subst H'
  have : nacg' = nacg := by with_unfolding_all exact eq_of_heq h2
  subst nacg'
  have : ips' = ips := by with_unfolding_all exact eq_of_heq h3
  subst ips'
  have : σ' = σ := by with_unfolding_all exact eq_of_heq h4
  subst σ'
  have : lam' = lam := by with_unfolding_all exact eq_of_heq h5
  subst lam'
  have : ε' = ε := by with_unfolding_all exact eq_of_heq h6
  subst ε'
  have : fr' = fr := by with_unfolding_all exact eq_of_heq h7
  subst fr'
  have : V' = V := by with_unfolding_all exact eq_of_heq hV
  subst V'
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  have : W₁ = c.W := by with_unfolding_all exact eq_of_heq c1
  subst W₁
  have : nW' = c.nW := by with_unfolding_all exact eq_of_heq c3
  subst nW'
  have : iW' = c.iW := by with_unfolding_all exact eq_of_heq c4
  subst iW'
  have : ρ₁ = c.ρ := by with_unfolding_all exact eq_of_heq c2
  subst ρ₁
  have : θ' = θ := by with_unfolding_all exact eq_of_heq hθ
  subst θ'
  have : ψ' = ψ := by with_unfolding_all exact eq_of_heq hψ
  subst ψ'
  have : BV' = BV := by with_unfolding_all exact eq_of_heq hBV
  subst BV'
  have : io' = io := by with_unfolding_all exact eq_of_heq hio
  subst io'
  have : ω' = ω := by with_unfolding_all exact eq_of_heq hω
  subst ω'
  have : v' = v := by with_unfolding_all exact eq_of_heq hv
  subst v'
  have : Δ' = Δ := by with_unfolding_all exact eq_of_heq hΔ
  subst Δ'
  exact (by with_unfolding_all exact (h0 :))

end Comparison₂

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}


private theorem delta_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') :
    HEq (RealDat.Delta i') (RealDat.Delta i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have hi : i' = i := Fin.ext h.symm
  subst i'
  exact (by with_unfolding_all exact ((HEq.refl (RealDat.Delta i)) :))

private theorem frames_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {ΛV : ∀ i, Submodule (𝓞 a.D.host.E) (Fin (Vc a.D i).rank → a.D.host.E)}
    {ΛV' : ∀ i, Submodule (𝓞 a'.D.host.E) (Fin (Vc a'.D i).rank → a'.D.host.E)} (hΛV : HEq ΛV' ΛV)
    {ΛW : ∀ i, Submodule (𝓞 a.D.host.E) (Fin (Wc a.D i).rank → a.D.host.E)}
    {ΛW' : ∀ i, Submodule (𝓞 a'.D.host.E) (Fin (Wc a'.D i).rank → a'.D.host.E)} (hΛW : HEq ΛW' ΛW)
    {βV : ∀ i, GL (Fin (Vc a.D i).rank) (Lev.EAf a.D)} {βV' : ∀ i, GL (Fin (Vc a'.D i).rank) (Lev.EAf a'.D)} (hβV : HEq βV' βV)
    {βW : ∀ i, GL (Fin (Wc a.D i).rank) (Lev.EAf a.D)} {βW' : ∀ i, GL (Fin (Wc a'.D i).rank) (Lev.EAf a'.D)} (hβW : HEq βW' βW) :
    HEq (ΛV' i') (ΛV i) ∧ HEq (ΛW' i') (ΛW i) ∧ HEq (βV' i') (βV i) ∧ HEq (βW' i') (βW i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have hi : i' = i := Fin.ext h.symm
  subst i'
  have : ΛV' = ΛV := by with_unfolding_all exact eq_of_heq hΛV
  subst ΛV'
  have : ΛW' = ΛW := by with_unfolding_all exact eq_of_heq hΛW
  subst ΛW'
  have : βV' = βV := by with_unfolding_all exact eq_of_heq hβV
  subst βV'
  have : βW' = βW := by with_unfolding_all exact eq_of_heq hβW
  subst βW'
  exact (by with_unfolding_all exact ((And.intro (HEq.refl (ΛV i)) (And.intro (HEq.refl (ΛW i)) (And.intro (HEq.refl (βV i)) (HEq.refl (βW i))))) :))

variable {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}

private def WeilAt1 {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (i : Fin D.R.m) : Prop :=
  IsWeilFull R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) ∧
  IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg (R.Q t) (R.xiR t) (R.vacP i) (R.vP i t) ∧
  IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (RealDat.Delta i) (R.ioP i)

private theorem exists_isOrbQuot_of_isHaarOn (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (hψ : HEq R'.ψ R.ψ) (hθ : HEq R'.θ R.θ) (hβW : HEq R'.βW R.βW) (hβV : HEq R'.βV R.βV) (hΛV : HEq R'.ΛV R.ΛV)
    (hΛW : HEq R'.ΛW R.ΛW) (hPg : HEq R'.Pg R.Pg)
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW) (hvac : HEq (R'.vacP i') (R.vacP i)) (hio : HEq (R'.ioP i') (R.ioP i))
    (hBV : HEq (R'.BV i') (R.BV i)) (hM : DSTie (R'.MW i' a'.D.what₂.embLL) (R.MW i a.D.what₂.embLL))
    (hω : HEq (R'.ωP i' t') (R.ωP i t)) (hv : HEq (R'.vP i' t') (R.vP i t))
    (hμ : HEq (R'.toLevCh.mu t' ((i' : ℕ) + 1)) (R.toLevCh.mu t ((i : ℕ) + 1))) (hη : HEq R'.eta R.eta)
    (hQ' : R'.Q t' = ∅) (hQ : R.Q t = ∅) (h0 : WeilAt1 R t i) : WeilAt1 R' t' i' := by
  have s : a.D.what₂.embLL = sg0 a.D A := (sgAt_mk _ R.hv0).symm
  have s' : a'.D.what₂.embLL = sg0 a'.D A' := (sgAt_mk _ R'.hv0).symm
  have hM0 : DSTie (R'.MW i' (sg0 a'.D A')) (R.MW i (sg0 a.D A)) := s ▸ s' ▸ hM
  have hW := wc_heq hP h
  have hV := vc_heq hP h
  obtain ⟨l1, l2, l3, l4⟩ := frames_heq hP h hΛV hΛW hβV hβW
  obtain ⟨w1, w2, w3⟩ := h0
  refine ⟨weilFull_of hP hV hW hψ hμ hη hω w1, ?_, ioW_of hP hV hW hM0 hθ hψ c1 c2 c3 c4 hBV hio hω hv (delta_heq hP h) w3⟩
  rw [hQ] at w2
  rw [hQ']
  exact thPVec_empty _ (thPVec_of hP hV hW hψ hθ (cart_heq hP hW hM0) l1 l2 l3 l4 hPg hvac hv (thPVec_empty _ w2))

end Fields

end GlobalTheory.Mem.R3.Rw.WeilAtExt

end

open GlobalTheory.Mem.R3.Rw.WeilAtExt in

theorem _root_.GlobalTheory.T.referenceTuple_weilDatum_vector_polynomialMap_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → z.R.toRealDat.ExAt → RSide z Wt' R' → LevSame z Wt' R' → WeilAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hEx hS hL i'
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  obtain ⟨⟨hψ, hθ, hβW, -, -, -, hβV, hΛV, hΛW, hPg, -, -, h1, -⟩, h2⟩ := hS
  obtain ⟨c1, c2, c3, c4, hvac, hio, hBV, m1, m2, m3, m4, m5, m6, m7, -⟩ := h1 i i' h
  obtain ⟨hω, hv, -⟩ := h2 i i' h
  obtain ⟨hμ, hη, hQ', hQ⟩ := hL
  have hb := RealDat.thP_of_weak z.pins.char.base.thP hEx
  exact exists_isOrbQuot_of_isHaarOn (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h hψ hθ hβW hβV hΛV hΛW hPg c1 c2 c3 c4 hvac hio hBV
    ⟨m1, m2, m3, m4, m5, m6, m7⟩ hω hv (hμ i i' h).1 hη hQ' hQ ⟨z.pins.char.fullP i _, hb.vP i _, hb.ioP i _⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleWeilDatumVectorPolynomialMapEnlarg =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBaseStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBaseStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

theorem _root_.GlobalTheory.T.thetaLift_at_reference_tuple_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → z.R.toRealDat.ExAt → RSide z Wt' R' → IdemSame z Xg → LiftAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftExt.liftAt_of_rSide
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBaseStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBase =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBase", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCopiesReferenceObjectsOverEnlargedBase\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersEStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormGroupsModelsActionsMeasuresBasesCharacterise\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBaseStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBaseStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandraStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDefiniteFormsLargerFieldCombinationSmall\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleHilbertModelDefiniteFormsEnlarged\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleWeilDatumVectorPolynomialMapEnlarg\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBaseStatement\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.WeilExt

theorem stepW_host_rank (p : WP) :
    StepW p fun _ B _ _ _ => ∀ X : Stages, X.B.toPre = B.toPre →
      HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV :=
  Step.of_evG (((evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).imp
    fun _ _ _ _ _ H _ _ _ hO _ _ _ _ _ X e => ⟨(H.2 X (e ▸ hO)).1, (H.1 X (e ▸ hO)).2⟩)

theorem isIdG_of_heq (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (hP : Pg = Pg') (h : HEq e e') (h' : IsPlacewiseIdentity X (px := px) e') : IsPlacewiseIdentity X (px := px) e := by
  subst hP
  obtain rfl := eq_of_heq h
  exact h'

theorem trans_eq_of_heq (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (c : G0 Pg X.toD7.R.r ≃* G0g X.toD7.nd) (c' : G0 Pg' X.toD7.R.r ≃* G0g X.toD7.nd)
    (hP : Pg = Pg') (h : HEq e e') (hc : HEq c c') : e.trans c = e'.trans c' := by
  subst hP
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hc
  rfl

private theorem updM_preserves_invariants {D : D7} {G : Type} [Group G] [Fintype G]
    {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) {F : Face D A3.A} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    (hPre : R.toRealDat.Pre0 F) (hIn : R.IsInert) (hTup : R.IsTup)
    (hKeep : Keep (A3 := A3) R.toRealDat F cG)
    (HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG) :
    let R' : RealDat3 D A3 Ks :=
      ⟨updM R.toRealDat HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG,
        R.plI, R.SF, R.phs, R.lam3⟩
    R'.toRealDat.Pre0 F ∧ R'.IsInert ∧ R'.IsTup ∧ Keep (A3 := A3) R'.toRealDat F cG := by
  exact ⟨realDatum_prerequisites_update_models hPre HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG,
    ⟨hIn.tie, hIn.onto, hIn.hR, hIn.hL, hIn.SF⟩,
    ⟨hTup.mu_off, hTup.mu_used, hTup.mu_ne, hTup.mu_conj, hTup.mu_on⟩,
    ⟨hKeep.std, hKeep.signs, hKeep.frames, hKeep.beta, hKeep.prX, hKeep.grp, hKeep.psi, hKeep.guard,
      hKeep.valKs, hKeep.frameKs, hKeep.levKs⟩⟩

section

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

theorem m_eq (hE : Enl0 B B') : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m :=
  show B'.toPre.R.m = B.toPre.R.m from congrArg (fun P => P.R.m) hE.1



theorem exists_rSide (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (hE : Enl0 B B') (h : RSideW z Wt' R₀) :
    ∃ HV νV fdV ωP vP thF thG, RSide z Wt' (⟨updM R₀.toRealDat R₀.HX HV R₀.HE R₀.gE R₀.jX (fun _ _ => 0) R₀.νY R₀.fdY R₀.ν0 R₀.fd0
      R₀.νX R₀.fdX νV fdV ωP vP thF thG, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ :
      RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) := by
  have key := fun i' : Fin (w'.st Z').toD7.R.m => GlobalTheory.T.exists_copies_reference_objects_over_enlarged_base z Wt' R₀ hE h (Fin.cast (m_eq hE) i') i' rfl
  choose ω v H th g ν fd k using key
  refine ⟨fun i _ => H i, fun i _ => ν i, fun i _ => fd i, fun i _ => ω i, fun i _ => v i, fun i _ => th i, fun i _ => g i, ?_, ?_⟩
  · delta RSideW at h ⊢
    with_unfolding_all exact (h :)
  · intro i i' e
    have e' : i = Fin.cast (m_eq hE) i' := Fin.ext e
    subst e'
    exact (by with_unfolding_all exact (k i' :))

end



theorem exists_pins_rSide : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀ →
        ∃ (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R') := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine (stepW_host_rank Pinned).trans (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf _ hpx Z hX Wt z hG _ hFine hHolds Z' hX' hG' _ _ core' alg' _ _ _ _ _ _ _ _
  intro Xg tr₀ R₀ cG hyp
  obtain ⟨hLev, hId, hGood, hMu, hIdem, hPre, hIn, hTup, hAll, hKeep, hBrg, hSide⟩ := hyp
  letI := alg'
  generalize {v | B'.places.resChar v ∈ T'.pl} = Wt' at *
  have hHH := (H (w'.st Z') rfl).1
  have hn := (H (w.st Z) hE.1.symm).2
  obtain ⟨HV, νV, fdV, ωP, vP, thF, thG, hS⟩ := exists_rSide z Wt' R₀ hE hSide
  generalize hR₁ : (⟨updM R₀.toRealDat R₀.HX HV R₀.HE R₀.gE R₀.jX (fun _ _ => 0) R₀.νY R₀.fdY R₀.ν0 R₀.fd0
      R₀.νX R₀.fdX νV fdV ωP vP thF thG, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ :
      RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀) core'.Q.c.F) = R₁ at hS
  have move : ∃ cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd,
      LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R₁.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₁.eG ∧
      GoodSet (w'.st Z') (px := w'.px) (R₁.eG.trans cG₁) Xg ∧ MuOf (w'.st Z') w'.I T' Wt' R₁.mu R₁.twPl ∧
      R₁.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀).lv2 ∧ R₁.IsInert ∧ R₁.IsTup ∧ R₁.AllPlaces ∧
      Keep R₁.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀).lv2 cG₁ ∧
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀ R₁.toRealDat := by
    subst hR₁
    have hUpd := updM_preserves_invariants R₀ hPre hIn hTup hKeep R₀.HX HV R₀.HE R₀.gE
      R₀.jX (fun _ _ => 0) R₀.νY R₀.fdY R₀.ν0 R₀.fd0 R₀.νX R₀.fdX νV fdV ωP vP thF thG
    refine ⟨cG, ?_, ?_, ?_, ?_, hUpd.1, hUpd.2.1, hUpd.2.2.1, ?_, hUpd.2.2.2, ?_⟩
    · exact hLev
    · exact hId
    · exact hGood
    · exact hMu
    · exact hAll
    · delta BrgStd at hBrg ⊢
      exact hBrg
  clear hR₁ hLev hId hGood hMu hPre hIn hTup hAll hKeep hBrg hSide
  obtain ⟨cG₁, hLev, hId, hGood, hMu, hPre, hIn, hTup, hAll, hKeep, hBrg⟩ := move
  have hSide₁ := hS.1
  have hL := GlobalTheory.T.liftCharacters_agree_over_enlarged_base z Wt' R₁ hE hf hpx hLev
  have hI := GlobalTheory.T.goodIdempotent_coefficients_agree_enlarged_base z Wt' R₁ hE hf hpx hG hG' hSide₁ cG₁ hKeep
  have hz := ratAt_of_geo z.R z.F z.pins.char hFine.1 hn z.geo hFine.2.1 hHolds.unif
  obtain ⟨tr, R, cG', hPins, hEx, hLevEq, hEG, hCG, hmu, htw, hBrg', hS', hSame⟩ :=
    charW_keep (w'.st Z') w'.px w'.I hX' (usedOf w'.I T' Wt') Xg tr₀ core'.Q.c.F R₁ cG₁ (GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra h5 h6 h7 h3 _) hIdem
      (fun R hP hc ht => GlobalTheory.ExAtAssembly.exAt_holds h1 h2 h3 h4 _ _ _ _ _ _ R hP.1.lev hP.1.fam hP.2 hP.1.record hHH hc ht)
      (fun R => RSideW z Wt' (⟨R, R₁.plI, R₁.SF, R₁.phs, R₁.lam3⟩ :
        RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr₀) core'.Q.c.F))
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s => by
        delta RSideW at s ⊢
        with_unfolding_all exact (s :))
      (fun _ _ _ _ _ _ _ _ _ _ _ _ s => by
        delta RSideW at s ⊢
        with_unfolding_all exact (s :))
      (fun _ _ _ s => by
        delta RSideW at s ⊢
        with_unfolding_all exact (s :))
      (by with_unfolding_all exact (hSide₁ :)) hPre hIn hTup hAll hKeep hBrg
      (GlobalTheory.T.finiteGroupCharacter_eq_product_residualCharacters_enlarged z Wt' R₁ hE hpx hSide₁ hL) (GlobalTheory.T.modW_of_rSideW z Wt' R₁ hE hpx hSide₁) (GlobalTheory.T.referenceTuple_weilDatum_vector_polynomialMap_enlarged z Wt' R₁ hE hFine.1 hS hL)
      (GlobalTheory.T.referenceTuple_hilbertModel_definiteForms_enlarged z Wt' R₁ hE hPre hS hL) (GlobalTheory.T.thetaLift_at_reference_tuple_over_enlarged_base z Wt' R₁ hE hpx hFine.1 hS hI)
      (GlobalTheory.T.referenceTuple_rationalForm_lifts_algebraic_enlarged z Wt' R₁ hE hS (GlobalTheory.T.rationalDefiniteForms_largerField_combination_smallerField z Wt' R₁ hE hf hpx hSide₁) hz)
  have hPg : R.Pg = R₁.Pg := congrArg LevCh.Pg hLevEq
  refine ⟨tr, R, cG', hPins, hLevEq ▸ hLev, isIdG_of_heq _ R.eG R₁.eG hPg hEG hId, ?_, ?_, hBrg', hEx, ?_, fun i i' e => ?_⟩
  · rw [trans_eq_of_heq _ R.eG R₁.eG cG' cG₁ hPg hEG hCG]; exact hGood
  · rw [hmu, htw]; exact hMu
  · delta RSideW at hS' ⊢
    with_unfolding_all exact (hS' :)
  · -- Project the conjuncts directly to avoid large eliminators in this dependent goal.
    have hRef := hS.2 i i' e
    have hSameAt := hSame i'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (heq_of_eq hSameAt.1).trans hRef.1
    · exact (heq_of_eq hSameAt.2.1).trans hRef.2.1
    · exact hSameAt.2.2.1.trans hRef.2.2.1
    · exact hSameAt.2.2.2.1.trans hRef.2.2.2.1
    · exact hSameAt.2.2.2.2.1.trans hRef.2.2.2.2.1
    · exact (heq_of_eq hSameAt.2.2.2.2.2.1).trans hRef.2.2.2.2.2.1
    · exact (heq_of_eq hSameAt.2.2.2.2.2.2).trans hRef.2.2.2.2.2.2

end GlobalTheory.Mem.R3.Rw.WeilExt

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBase =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBaseStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBaseStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver\npublic import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBase\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterisedDataWeilEnlargedBaseStatement =====
