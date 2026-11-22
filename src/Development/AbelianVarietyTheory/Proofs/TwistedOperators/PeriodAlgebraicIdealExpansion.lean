import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJetsOfTranslateJets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGfCOfSuppAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BottomFieldDict

theorem det_X_isHomogeneous {σ : Type*} {a : ℕ} (f : Fin a → Fin a → σ) :
    (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)).det.IsHomogeneous a := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun e _ => ?_)
  have h1 : (∏ i, (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)) (e i) i).IsHomogeneous
      (∑ _i : Fin a, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X ℂ _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
  have h0 : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)).IsHomogeneous 0 := by
    have : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)) = MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : ℂ) := by simp
    rw [this]; exact MvPolynomial.isHomogeneous_C _ _
  simpa using h0.mul h1

theorem minorPol_isHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n) :
    (GlobalTheory.NormSum.minorPol D T).IsHomogeneous (a * ∑ τ, n τ) := by
  unfold GlobalTheory.NormSum.minorPol
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset D.what₂.Tau)
    (fun τ => ∏ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, ((T τ j) : Fin a → Fin d) i, i') :
      MvPolynomial (GL3Theta.Idx D a d) ℂ)).det) (fun τ => ∑ _j : Fin (n τ), a) (fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => det_X_isHomogeneous _))
  convert h using 1
  simp [Finset.mul_sum, mul_comm]

theorem card_of_mem_support {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n)
    {α : TaylorLogMetric.Mono D a d} (hα : α ∈ (GlobalTheory.NormSum.minorPol D T).support) :
    Multiset.card (Finsupp.toMultiset α) = a * ∑ τ, n τ := by
  have h := minorPol_isHomogeneous T (MvPolynomial.mem_support_iff.mp hα)
  rw [Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem minorPol_coeff_isAlgebraic {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : GlobalTheory.NormSum.Tup D a d n)
    (α : GL3Theta.Idx D a d →₀ ℕ) : IsAlgebraic ℚ ((GlobalTheory.NormSum.minorPol D U).coeff α) := by
  have e : GlobalTheory.NormSum.minorPol D U = MvPolynomial.map (algebraMap ℚ ℂ) (∏ τ, ∏ j, (Matrix.of fun i i' : Fin a =>
      (MvPolynomial.X (τ, (U τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℚ)).det) := by
    unfold GlobalTheory.NormSum.minorPol
    simp only [map_prod, RingHom.map_det]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
    congr 1
    ext1 i i'
    simp
  rw [e, MvPolynomial.coeff_map]
  exact isAlgebraic_algebraMap _

theorem apply_minorPol {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : GlobalTheory.NormSum.Tup D a d n)
    (l : MvPolynomial (GL3Theta.Idx D a d) ℂ →ₗ[ℂ] ℂ) (c p ζ : ℂ) (G : TaylorLogMetric.VC D a d → ℂ)
    (h : ∀ k : GL3Theta.Idx D a d →₀ ℕ, l (MvPolynomial.monomial k 1) =
      c * (p ^ (k.sum fun _ e => e) * (ζ * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G))) :
    l (GlobalTheory.NormSum.minorPol D U) = c * p ^ (a * ∑ τ, n τ) * (ζ * GL3Theta.applyAt0 D (GlobalTheory.NormSum.minorPol D U) G) := by
  conv_lhs => rw [(GlobalTheory.NormSum.minorPol D U).as_sum]
  rw [map_sum l, GL3Theta.applyAt0, Finset.mul_sum _ _ ζ, Finset.mul_sum _ _ (c * p ^ (a * ∑ τ, n τ))]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := card_of_mem_support U hα
  rw [Finsupp.card_toMultiset] at hk
  have e : (MvPolynomial.monomial α ((GlobalTheory.NormSum.minorPol D U).coeff α) : MvPolynomial (GL3Theta.Idx D a d) ℂ) =
      (GlobalTheory.NormSum.minorPol D U).coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hk' : (α.sum fun _ e => e) = a * ∑ τ, n τ := hk
  rw [e, map_smul, h, GlobalTheory.FockPos.applyAt0_monomial', hk', smul_eq_mul]
  ring

theorem lat_eq_colLat {D : D7} {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) :
    (r.Λ : Set (Fin V.rank → D.host.E)) = (colLat (1 : GL (Fin V.rank) D.host.E) : Set (Fin V.rank → D.host.E)) := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, h.2.1, lc_mem_colLat_one]
  simp only [Submodule.mem_one]

theorem lat_eq_inV {D : D7} {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) :
    (r.Λ : Set (Fin V.rank → D.host.E)) = GlobalTheory.MovedDict.inV 1 (StandardLatticesGL3.stdL D V.rank) := by
  ext y
  rw [SetLike.mem_coe, h.2.1]
  simp [GlobalTheory.MovedDict.inV, StandardLatticesGL3.stdL, Submodule.mem_pi, Submodule.mem_one]

end GlobalTheory.BottomFieldDict

end
