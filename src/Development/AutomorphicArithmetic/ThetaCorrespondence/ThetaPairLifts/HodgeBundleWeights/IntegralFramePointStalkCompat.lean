import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkCompat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ArchimedeanSectionIntegralFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatValZero
section Gen
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
theorem twisted_section_flat_valuation (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hL : Laws U x) (hFE : FlatExists U x) (Z : Comp Xo c)
    (w : Psi H → ℤ) : ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), ∀ (T : CDVR) (io : c.F →+* T.Fr)
      (y : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → evI y (idem Z) ≠ 0 → vV T.V (evI y t.sig) = 0 := by
  have hp : HasPts U Z := GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z
  let sF : ∀ τ, FlatSec U x Z τ := fun τ => (hFE.nonempty Z τ).some
  have hK := nonempty_keySec hL
  let s := FlatSec.shift hp sF w
  have hδ := GlobalTheory.FlatTwisting.finite_sum_flDefect (Dw := Dw) (c := c) w
  refine ⟨TwSec.ofConst s (by convert hδ) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos s) fun G hG f hf => ?_,
    fun T io y hio hZ => ?_⟩
  · have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos (w := -w) (s.symm.copy rfl rfl)
      (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
    rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
    exact h
  letI := io.toAlgebra
  have hLies : LiesOn Z y.1 := by
    by_contra hn
    exact hZ ((idem_mem_suppOn Z) T.Fr y.1 ((liesOff_iff Z y.1).2 hn))
  have hid : evI y (idem Z) = 1 := by
    have e := evI_mul y (idem Z) (idem Z)
    rw [idem_mul_idem] at e
    exact mul_left_cancel₀ hZ (by rw [mul_one]; exact e.symm)
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hsig : ∀ τ, ev (sF τ).sig ∈ unitsV T := fun τ => by
    have hn := _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt hP hP.q2 E H Dw l Xo c r U x hL Z τ
      (ArchSec.ofConst (sF τ)) T io y hio hLies
    have hev0 : evI y (sF τ).sig ≠ 0 := by
      intro h0
      rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, h0, nval_zero] at hn
      exact EReal.top_ne_zero hn
    refine ⟨hev0, ?_⟩
    rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, nval_of_ne hev0] at hn
    have : ((vV T.V (evI y (sF τ).sig) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) = 0 := by exact_mod_cast hn
    show vV T.V (evI y (sF τ).sig) = 0
    simpa using this
  have hinv : ∀ τ, ev (sF τ).inv ∈ unitsV T := fun τ => by
    have e : ev (sF τ).sig * ev (sF τ).inv = 1 := by
      rw [← map_mul, (sF τ).mul_inv]; exact hid
    have h2 : ev (sF τ).inv ≠ 0 := right_ne_zero_of_mul_eq_one e
    refine ⟨h2, ?_⟩
    have h3 := vV_mul (V := T.V) (hsig τ).1 h2
    rw [e, (hsig τ).2, zero_add, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    exact h3.symm
  have hprod : ev s.sig ∈ unitsV T := by
    rw [(FlatSec.shift_spec hp sF w).1, map_mul, map_prod]
    refine (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).prod_mem fun τ _ => ?_)
    rw [(ConstSec.zpow_spec (sF τ) (-w τ)).1, map_mul, map_mul, map_pow, map_pow]
    exact (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).mul_mem ((unitsV T).pow_mem (hsig τ) _) ((unitsV T).pow_mem (hinv τ) _))
  exact hprod.2
end Gen
end GlobalTheory.FlatValZero
open GlobalTheory.FlatValZero
end
end

