import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.FourierCoeffIntSt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PerfectPairings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings

namespace GlobalTheory.FourierChainCompare

section Duality

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]

theorem linearIndependent_addChar (A K : Type) [AddCommGroup A] [Field K] :
    LinearIndependent K (fun χ : AddChar A K => (χ : A → K)) :=
  (linearIndependent_monoidHom (Multiplicative A) K).comp AddChar.toMonoidHomEquiv
    AddChar.toMonoidHomEquiv.injective

theorem finite_addChar (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    Finite (AddChar A K) := (linearIndependent_addChar A K).finite

theorem card_addChar_le (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    Nat.card (AddChar A K) ≤ Fintype.card A := by
  haveI := finite_addChar A K
  letI := Fintype.ofFinite (AddChar A K)
  rw [Nat.card_eq_fintype_card]
  simpa using (linearIndependent_addChar A K).fintype_card_le_finrank

theorem pairing_zero {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) : e 0 t = 1 := by
  have h := he.add_left 0 0 t
  rw [add_zero] at h
  exact left_eq_mul.mp h

def chr {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) : AddChar A K where
  toFun a := ((e a t : Kˣ) : K)
  map_zero_eq_one' := by rw [pairing_zero he, Units.val_one]
  map_add_eq_mul' a a' := by rw [he.add_left, Units.val_mul]

theorem chr_apply {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) (a : A) :
    chr he t a = ((e a t : Kˣ) : K) := rfl

theorem chr_injective {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Function.Injective (chr he) := by
  intro t t' h
  refine sub_eq_zero.mp (he.nondeg_right _ fun a => ?_)
  have h1 : e a t = e a t' := Units.ext (DFunLike.congr_fun h a)
  have h2 := he.add_right a (t - t') t'
  rw [sub_add_cancel, h1] at h2
  exact right_eq_mul.mp h2

variable [Fintype A] [Fintype B]

end Duality

section Chain

variable {R : Type} [CommRing R] {d : ℕ}

theorem act_zero {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : A.act 0 = 0 := by
  have hc := A.const 0
  have h1 : A.act 0 = G.add (A.act 0) (A.act 0) := by rw [← A.add_act, add_zero]
  have h2 : A.act 0 = comp1 (A.act 0) (A.act 0) := by rw [← A.mul_act, mul_zero]
  have h3 : dLin (A.act 0) = 0 := by
    have := GlobalTheory.FormalMulN.dLin_add G hc hc
    rw [← h1] at this
    exact left_eq_add.mp this
  have h4 : ∀ i, 2 ≤ (A.act 0 i).order := fun i =>
    GlobalTheory.FormalSeries.two_le_order_iff.mpr ⟨hc i, fun j => by
      obtain ⟨j0, j⟩ := j
      obtain rfl : j0 = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun h3 i) j⟩
  have h5 : ∀ (k : ℕ) i, (k : ℕ∞) ≤ (A.act 0 i).order := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      have := GlobalTheory.FormalSeries.le_order_subst_sub_subst
        (a := fun p : Fin 1 × Fin d => (![A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) (b := 0) (k := k)
        (fun p => GlobalTheory.GaugeAdjoint.const_one hc p.1 p.2) (by simp)
        (fun p => by simpa using ih p.2) (h4 i)
      rw [subst_zero_of_constantCoeff_zero (hc i), sub_zero] at this
      rw [congrFun h2 i]
      exact this
  funext i
  exact GlobalTheory.FormalSeries.eq_of_forall_le_order_sub fun k => by simpa using h5 k i

end Chain

end GlobalTheory.FourierChainCompare
