import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Twhopf

theorem valAt_restrict {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s := PositivityTheory.HtPt.Unc.valAt_restrict x i hV hU s

theorem top_le_of_le {Y X : Scheme.{0}} (x : Y ⟶ X) {U V : X.Opens} (i : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ U := fun _ hz => i (hV hz)

theorem top_le_of_mem {K : Type} [Field K] {X : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens}
    (z : Spec (CommRingCat.of K)) (hz : x z ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := PositivityTheory.HtPt.Unc.top_le_of_mem x z hz

theorem sec_inj : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 := PositivityTheory.HtPt.Unc.sec_inj

theorem reg_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t := PositivityTheory.HtPt.Unc.reg_iff

section ops

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)

theorem regularAt_const (r : R) (g : Γ.G.left) : Γ.RegularAt (fun _ => algebraMap R _ r) g :=
  ⟨⊤, trivial, RegDenom.structHom Γ.G.hom ⊤ r, fun t h =>
    RegDenom.valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t)) ⊤ h r⟩

theorem regularAt_add_mul {f f' : T → FractionRing R} {g : Γ.G.left} (h : Γ.RegularAt f g)
    (h' : Γ.RegularAt f' g) :
    Γ.RegularAt (fun t => f t + f' t) g ∧ Γ.RegularAt (fun t => f t * f' t) g := by
  obtain ⟨U, hU, s, hs⟩ := h
  obtain ⟨V, hV, s', hs'⟩ := h'
  let a := (Γ.G.left.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom s
  let b := (Γ.G.left.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom s'
  have ha : ∀ t h, valAt (Γ.pt t).left (U ⊓ V) h a = f t := fun t h =>
    (valAt_restrict _ _ h (top_le_of_le _ inf_le_left h) _).trans (hs t _)
  have hb : ∀ t h, valAt (Γ.pt t).left (U ⊓ V) h b = f' t := fun t h =>
    (valAt_restrict _ _ h (top_le_of_le _ inf_le_right h) _).trans (hs' t _)
  refine ⟨⟨U ⊓ V, ⟨hU, hV⟩, a + b, fun t h => ?_⟩, ⟨U ⊓ V, ⟨hU, hV⟩, a * b, fun t h => ?_⟩⟩
  · rw [← SubOrder.valHom_apply, map_add, SubOrder.valHom_apply, SubOrder.valHom_apply, ha, hb]
  · rw [← SubOrder.valHom_apply, map_mul, SubOrder.valHom_apply, SubOrder.valHom_apply, ha, hb]

def btSub (U : Γ.G.left.Opens) : Subalgebra R (T → R) where
  carrier := Γ.btSet U
  mul_mem' hf hf' t g hg := by
    simpa only [Pi.mul_apply, map_mul] using (regularAt_add_mul Γ (hf t g hg) (hf' t g hg)).2
  add_mem' hf hf' t g hg := by
    simpa only [Pi.add_apply, map_add] using (regularAt_add_mul Γ (hf t g hg) (hf' t g hg)).1
  algebraMap_mem' r _ g _ := regularAt_const Γ r g

end ops

theorem mem_order : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U := by
  intro R _ _ T _ _ Γ U f
  exact ⟨fun h => Algebra.adjoin_le (S := btSub Γ U) (fun _ hx => hx) h, fun h => Algebra.subset_adjoin h⟩

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder in

theorem sub_order : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∃ (H : Subgroup T) (A : Subalgebra R (H → R)), (∀ t, t ∈ H ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsHopfOrder A ∧ ∀ f : H → R, f ∈ A ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : H) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub

theorem regularAt_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left), (Γ.G.hom g).asIdeal = ⊥ → Γ.RegularAt f g := by
  intro R _ _ T _ _ Γ f g hg
  obtain ⟨d, hd, U, hU, s, hs⟩ := RegDenom.exists_denom_regularAt R T Γ f g
  let c : Γ(Γ.G.left, U) := RegDenom.structHom Γ.G.hom U d
  have hgW : g ∈ Γ.G.left.basicOpen c := by
    have e := Scheme.basicOpen_appLE Γ.G.hom U ⊤ (RegDenom.le_preimage_top Γ.G.hom U)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv d)
    rw [basicOpen_eq_of_affine] at e
    have e' : Γ.G.left.basicOpen c = _ := e
    rw [e']
    refine ⟨hU, ?_⟩
    change d ∉ (Γ.G.hom g).asIdeal
    rw [hg]
    exact hd
  let ρ := (Γ.G.left.presheaf.map (homOfLE (Γ.G.left.basicOpen_le c)).op).hom
  have hu : IsUnit (ρ c) := Γ.G.left.toRingedSpace.isUnit_res_basicOpen c
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  refine ⟨_, hgW, w * ρ s, fun t h => ?_⟩
  have hU' := top_le_of_le _ (Γ.G.left.basicOpen_le c) h
  have e1 : valAt (Γ.pt t).left _ h (ρ s) = algebraMap R _ d * f t :=
    (valAt_restrict _ _ h hU' _).trans (hs t hU')
  have e2 : valAt (Γ.pt t).left _ h (ρ c) = algebraMap R _ d :=
    (valAt_restrict _ _ h hU' _).trans (RegDenom.valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t)) U hU' d)
  have e3 := congrArg (SubOrder.valHom (Γ.pt t).left _ h) hw
  rw [map_mul, map_one, SubOrder.valHom_apply _ _ _ (ρ c), e2] at e3
  rw [← SubOrder.valHom_apply, map_mul, SubOrder.valHom_apply _ _ _ (ρ s), e1, ← _root_.mul_assoc, e3, _root_.one_mul]

end PositivityTheory.HtPt.Twhopf
