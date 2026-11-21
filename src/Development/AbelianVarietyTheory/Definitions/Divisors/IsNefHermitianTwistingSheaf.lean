import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.VolBr.Model

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

section Two

variable (A : HermLB p) (u : A.B.Sec) (hu : genericPoint X ∈ nonzeroLocus u)

abbrev dbl : Pair p := ⟨A, A, ratOfSec u hu, ratOfSec u hu, isRatSec_ratOfSec u hu, isRatSec_ratOfSec u hu⟩

variable {A u hu}

end Two

omit [IsIntegral X] in

theorem isNef_of_small {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (hs : L.SemiPos D) (hf : ArInt.NefFib L)
    (hg : ∀ x : X, ∃ u ∈ L.smallSec, x ∈ nonzeroLocus u) : L.IsNef D where
  semiPos := hs
  vertical := hf
  horizontal Z i _ _ _ hc hd := by
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
    obtain ⟨u, hu, ha⟩ := hg (i (genericPoint Z))
    have hgen : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
      rw [GlobalTheory.nonzeroLocus_secPull]; exact ha
    have h0 : ∀ σ (y : CxPts (i ≫ p) σ), y ∈ ptsIn _ σ (nonzeroLocus (GlobalTheory.secPull u i)) := fun σ y => by
      refine mem_ptsIn.2 ?_
      have key : ∀ y : Sp ℂ ⟶ Z, y (IsLocalRing.closedPoint ℂ) = genericPoint Z := fun y =>
        GlobalTheory.HtSelfInter.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
      rw [key]
      exact hgen
    refine ⟨_, isRatSec_ratOfSec _ hgen, ?_⟩
    rw [HermLB.curveDeg_sec i u hgen h0]
    refine sub_nonneg.2 (le_trans (b := 0) ?_ ?_)
    · refine finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun σ =>
        finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun y => ?_
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (Weight.nsq_nonneg _ _ _) (hu σ _)) zero_le_two
    · exact finsum_nonneg fun z =>
        mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)

local instance isIntegral_line : IsIntegral (PSpace ℤ 1) := isIntegral_of_isDomain ℤ 1

end GlobalTheory.VolBr.Model
