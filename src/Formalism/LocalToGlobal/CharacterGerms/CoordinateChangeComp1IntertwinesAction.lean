import Formalism.LocalToGlobal.CharacterGerms.FirstPartialLawAtPoints

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

variable (Y : FBChart C V O dd)

theorem coordinateChange_comp1_intertwines_action {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.A.act x) a = actAt Y x a := by
  unfold actAt
  unfold comp1
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; simp)
  | (congr 1; funext q; skip)

theorem addOf_eq' {n : ℕ} (a b : Pt C n dd) : addOf Y.B.G.F a b = addAt Y a b := by
  unfold addAt
  unfold addOf
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; unfold P2; rfl)
  | (congr 1; funext q; unfold P2; obtain ⟨j, k⟩ := q; fin_cases j <;> simp)

theorem actAt_addAt (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    actAt Y x (addAt Y a b) = addAt Y (actAt Y x a) (actAt Y x b) := by
  have h := Y.B.A.hom x
  rw [show Y.B.G.add (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) = addAt Y (pt C dd 0) (pt C dd 1) from addOf_eq' Y _ _,
    show Y.B.G.add (comp1 (Y.B.A.act x) (pt C (n := 2) dd 0)) (comp1 (Y.B.A.act x) (pt C (n := 2) dd 1)) =
      addAt Y (comp1 (Y.B.A.act x) (pt C dd 0)) (comp1 (Y.B.A.act x) (pt C dd 1)) from addOf_eq' Y _ _,
    coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  funext i
  have h2 := congrArg (MvPowerSeries.subst (P2 a b)) (congrFun h i)
  rw [actAt_subst Y hP (cc_addAt Y k0 k1), addAt_subst Y hP (cc_actAt Y x k0) (cc_actAt Y x k1)] at h2
  have e2 : (fun i => MvPowerSeries.subst (P2 a b) (addAt Y (pt C dd (0 : Fin 2)) (pt C dd (1 : Fin 2)) i)) =
      addAt Y a b := by
    funext j
    rw [addAt_subst Y hP k0 k1, e0, e1]
  have e3 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (0 : Fin 2)) i)) = actAt Y x a := by
    funext j
    rw [actAt_subst Y hP k0, e0]
  have e4 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (1 : Fin 2)) i)) = actAt Y x b := by
    funext j
    rw [actAt_subst Y hP k1, e1]
  rw [e2, e3, e4] at h2
  exact h2

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
