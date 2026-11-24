module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

abbrev nc_iota (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : Formalism.MainNotions.G.HH D :=
  t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)

include hL ht0 in
theorem nc_n_eq : (D.gat u w hg).P.n' (Y.vOf u w hg t0) = addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  exact (h t0 ht0).1

include hL ht0 in
theorem nc_iota_inj : Function.Injective (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  intro s s' hss
  have hs := lt_of_lt_of_eq s.isLt hn
  exact Fin.ext (nsmul_injOn_Iio_addOrderOf hs (lt_of_lt_of_eq s'.isLt hn) (add_left_cancel hss))

include hL ht0 in
theorem nc_topsOn : Formalism.MainNotions.G.topsOn X (D.what₂.places.resChar w) t0 =
    ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).image (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  have hsg : ¬ G.IsSg D (D.what₂.places.resChar w) := by
    unfold G.IsSg
    rw [hg.2.2.1]
    decide
  have hst : G.stepP D (D.what₂.places.resChar w) = G.hP D (D.what₂.places.resChar w) := by
    unfold G.stepP
    exact ite_eq_right hsg
  let step := G.hP D (D.what₂.places.resChar w)
  have hiter (t : G.HH D) (i : ℕ) : X.bs step (t + i • step) = X.bs step t := by
    induction i with
    | zero => simp
    | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]
  have hr : t0 ∈ Finset.univ.image (X.bs step) := by
    simpa only [G.reps, hst] using ht0
  have hb : X.bs step t0 = t0 := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i, hi⟩ := X.bs_orb step t
    simpa only [hi] using (hiter (X.bs step t) i).symm
  have hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := addOrderOf_pos _
  ext t
  simp only [Formalism.MainNotions.G.topsOn, Finset.mem_filter, Finset.mem_image, hst]
  constructor
  · rintro ⟨htT, hbt⟩
    obtain ⟨i, hi⟩ := X.bs_orb (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) t
    rw [hbt] at hi
    have hlt : i % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) <
        (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by
      rw [hn]; exact Nat.mod_lt _ hpos
    refine ⟨⟨_, hlt⟩, ?_, ?_⟩
    · rw [((h t0 ht0).2 _).2.1]
      simpa only [mod_addOrderOf_nsmul, hi] using htT
    · simp only [nc_iota, mod_addOrderOf_nsmul, hi]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨((h t0 ht0).2 s).2.1.1 hs, ?_⟩
    simp only [nc_iota]
    change X.bs step (t0 + s.val • step) = t0
    rw [hiter, hb]

include hL ht0 in
theorem nc_isV (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) :
    Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) ↔ ¬ IsOddPos s := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have hsg : ¬ G.IsSg D (D.what₂.places.resChar w) := by
    unfold G.IsSg
    rw [hg.2.2.1]
    decide
  have hst : G.stepP D (D.what₂.places.resChar w) = G.hP D (D.what₂.places.resChar w) := by
    unfold G.stepP
    exact ite_eq_right hsg
  let step := G.hP D (D.what₂.places.resChar w)
  have hiter (t : G.HH D) (i : ℕ) : X.bs step (t + i • step) = X.bs step t := by
    induction i with
    | zero => simp
    | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]
  have hr : t0 ∈ Finset.univ.image (X.bs step) := by
    simpa only [G.reps, hst] using ht0
  have hb : X.bs step t0 = t0 := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i, hi⟩ := X.bs_orb step t
    simpa only [hi] using (hiter (X.bs step t) i).symm
  have hnP : Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) =
      addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
    simp only [Formalism.MainNotions.G.nP, ite_eq_right hsg]
  have hs := lt_of_lt_of_eq s.isLt hn
  have key : ¬ IsOddPos s ↔ Even s.val := by
    show ¬ (s.val % 2 = 1) ↔ _
    rw [← Nat.odd_iff, Nat.not_odd_iff_even]
  rw [key]
  have hbs : X.bs (G.hP D (D.what₂.places.resChar w))
      (t0 + s.val • G.hP D (D.what₂.places.resChar w)) = t0 := (hiter t0 s.val).trans hb
  simp only [Formalism.MainNotions.G.IsV, hst, hnP, nc_iota, hbs]
  constructor
  · rintro ⟨i, hi, hev, heq⟩
    have hi' := nsmul_injOn_Iio_addOrderOf hi hs (add_left_cancel heq)
    rwa [← hi']
  · exact fun hev => ⟨s.val, hs, hev, rfl⟩

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
