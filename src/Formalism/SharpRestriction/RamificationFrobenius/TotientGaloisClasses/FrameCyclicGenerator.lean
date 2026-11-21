import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

namespace Frame

section Of

variable {A' : Type} [AddCommGroup A'] (e : ℕ) {n : ℕ} (ε : Idx n ≃ A') (h' : A' →+ Additive (HGrp e))
  (hs : Function.Surjective h') (a' : A') (hk : ∀ k : ℤ, h' (k • a') = 0 → k • a' = 0)

def ofEquiv : Frame :=
  letI : AddCommGroup (Idx n) := ε.addCommGroup
  { e := e
    ord := n
    grp := ε.addCommGroup
    h0 := h'.comp ε.addEquiv.toAddMonoidHom
    projection_surjective_field := hs.comp ε.surjective
    gen0 := ε.symm a'
    zsmul_generator_eq_zero_of_projection := fun k hk0 => by
      have h1 : ε.addEquiv (k • ε.symm a') = k • a' := by
        rw [map_zsmul]
        exact congrArg (fun x => k • x) (ε.apply_symm_apply a')
      apply ε.addEquiv.injective
      rw [h1, map_zero]
      apply hk
      rw [← h1]
      exact hk0 }

def ofEquivIso : (ofEquiv e ε h' hs a' hk).A ≃+ A' :=
  letI : AddCommGroup (Idx n) := ε.addCommGroup
  ε.addEquiv

theorem ofEquivIso_apply (t : (ofEquiv e ε h' hs a' hk).A) : ofEquivIso e ε h' hs a' hk t = ε t := rfl

theorem ofEquiv_h (t : (ofEquiv e ε h' hs a' hk).A) :
    (ofEquiv e ε h' hs a' hk).h t = h' (ofEquivIso e ε h' hs a' hk t) := rfl

theorem ofEquiv_generator : ofEquivIso e ε h' hs a' hk (ofEquiv e ε h' hs a' hk).a0 = a' :=
  ε.apply_symm_apply a'

theorem ofEquiv_order : (ofEquiv e ε h' hs a' hk).n0 = addOrderOf a' := by
  show addOrderOf (ofEquiv e ε h' hs a' hk).a0 = _
  conv_rhs => rw [← ofEquiv_generator e ε h' hs a' hk]
  exact (addOrderOf_injective (ofEquivIso e ε h' hs a' hk).toAddMonoidHom
    (ofEquivIso e ε h' hs a' hk).injective _).symm

variable [Fintype A']

def ofGroup : Frame := ofEquiv e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk

def ofGroupIso : (ofGroup e h' hs a' hk).A ≃+ A' :=
  ofEquivIso e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk

theorem ofGroup_e : (ofGroup e h' hs a' hk).e = e := rfl

theorem ofGroup_ord : (ofGroup e h' hs a' hk).ord = Fintype.card A' := rfl

theorem ofGroup_h (t : (ofGroup e h' hs a' hk).A) :
    (ofGroup e h' hs a' hk).h t = h' (ofGroupIso e h' hs a' hk t) := rfl

theorem ofGroup_generator : ofGroupIso e h' hs a' hk (ofGroup e h' hs a' hk).a0 = a' :=
  ofEquiv_generator e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk

theorem ofGroup_order : (ofGroup e h' hs a' hk).n0 = addOrderOf a' :=
  ofEquiv_order e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk

end Of

end Frame

def cycIso (e : ℕ) : Multiplicative (ZMod (2 ^ e)) ≃* HGrp e :=
  Classical.choose (hostGroup e).2.2.2.2.2.2.2.2

def cycHom (e : ℕ) : ZMod (2 ^ e) →+ Additive (HGrp e) :=
  AddMonoidHom.mk' (fun i => Additive.ofMul (cycIso e (Multiplicative.ofAdd i))) (fun i j => by
    rw [ofAdd_add, map_mul, ofMul_mul])

theorem cycHom_bijective (e : ℕ) : Function.Bijective (cycHom e) := by
  show Function.Bijective (fun i => Additive.ofMul (cycIso e (Multiplicative.ofAdd i)))
  exact Additive.ofMul.bijective.comp ((cycIso e).bijective.comp Multiplicative.ofAdd.bijective)

def idxZMod (n : ℕ) [NeZero n] : Idx n ≃ ZMod n := (ZMod.finEquiv n).toEquiv

theorem cycHom_ker (e : ℕ) (a' : ZMod (2 ^ e)) (k : ℤ) (hk : cycHom e (k • a') = 0) : k • a' = 0 :=
  (cycHom_bijective e).1 (by rw [hk, map_zero])

def frameCyc (e : ℕ) (a' : ZMod (2 ^ e)) : Frame :=
  Frame.ofEquiv e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')

def frameCycIso (e : ℕ) (a' : ZMod (2 ^ e)) : (frameCyc e a').A ≃+ ZMod (2 ^ e) :=
  Frame.ofEquivIso e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')

section Cyc

variable (e : ℕ) (a' : ZMod (2 ^ e))

theorem frameCyc_e : (frameCyc e a').e = e := rfl

theorem frameCyc_ord : (frameCyc e a').ord = 2 ^ e := rfl

theorem frameCyc_h_injective : Function.Injective (frameCyc e a').h := by
  intro x y hxy
  have h1 : ∀ t, (frameCyc e a').h t = cycHom e (frameCycIso e a' t) := fun t => rfl
  rw [h1, h1] at hxy
  exact (frameCycIso e a').injective ((cycHom_bijective e).1 hxy)

theorem frameCyclic_order : (frameCyc e a').n0 = addOrderOf a' :=
  Frame.ofEquiv_order e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')

end Cyc

def cyclicFrame (e : ℕ) : Frame := frameCyc e 1

theorem cyclicFrame_order (e : ℕ) : (cyclicFrame e).n0 = 2 ^ e := by
  show (frameCyc e 1).n0 = _
  rw [frameCyclic_order, ZMod.addOrderOf_one]

theorem cyclicFrame_index (e : ℕ) : (cyclicFrame e).o = 1 := by
  show (frameCyc e 1).ord / (frameCyc e 1).n0 = 1
  rw [frameCyclic_order, ZMod.addOrderOf_one, frameCyc_ord]
  exact Nat.div_self (pow_pos two_pos e)

end Formalism.HC

end
