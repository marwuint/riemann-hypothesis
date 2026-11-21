import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TypePreservedOfAdmissibleIntegral

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw.Model

open GlobalTheory.TwAll GlobalTheory.TwAll.Model

variable (D : D7)

instance finG : Finite (G0g D.nd) := by
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  infer_instance

abbrev Pt (j : ℕ) : Type := {_g : G0g D.nd // j ∈ Finset.Icc 1 D.R.m}

instance finPt (j : ℕ) : Fintype (Pt D j) := Fintype.ofFinite _

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

@[reducible] def tw : @NTw D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd :=
  { D.ntw with
    B := fun i j _ => Pt D j → D.ntw.O i
    acgB := fun _ _ _ => inferInstance
    modB := fun _ _ _ => inferInstance
    freeB := fun _ _ _ => inferInstance
    finB := fun _ _ _ => inferInstance
    Theta := fun _ _ _ => ⊤
    ThetaPsi := fun _ _ _ _ _ _ => ⊤
    ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_top _).symm
    hk := fun _ _ _ _ _ => 1
    hk_zero := fun _ _ _ _ => rfl
    hEig := fun _ _ _ _ => 1 }

def transl (i : D.ntw.Tw) (j : ℕ) : G0g D.nd →* ((Pt D j → KK D i) ≃ₗ[KK D i] (Pt D j → KK D i)) where
  toFun g :=
    { toFun := fun f y => f ⟨y.1 * g, y.2⟩
      invFun := fun f y => f ⟨y.1 * g⁻¹, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun f => by funext y; simp
      right_inv := fun f => by funext y; simp }
  map_one' := by ext f y; simp
  map_mul' g h := by ext f y; simp [mul_assoc]

def intF (i : D.ntw.Tw) (j : ℕ) : (Pt D j → D.ntw.O i) →ₗ[D.ntw.O i] (Pt D j → KK D i) :=
  (Algebra.linearMap (D.ntw.O i) (KK D i)).compLeft _

variable (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)

@[reducible] def ex : @NExp D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D) :=
  { D.nexp with
    Fm := fun i j _ => Pt D j → KK D i
    acgFm := fun _ _ _ => inferInstance
    modFmK := fun _ _ _ => inferInstance
    modFmO := fun _ _ _ => inferInstance
    towFm := fun _ _ _ => inferInstance
    fdFm := fun _ _ _ => inferInstance
    actG := fun i j _ => transl D i j
    U := ⊥
    psiU := fun _ _ => 1
    Bsup := fun i j _ => LinearMap.range (intF D i j)
    Dat := fun i j _ => Pt D j → KK D i
    th := fun _ _ _ a => a
    lev := fun _ _ _ _ => ∅
    thPsi := fun i _ _ k _ _ a => {(1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] a}
    thPsi_one := fun _ _ _ _ _ => rfl
    thU := fun i _ _ Q M a => (s i M • a) ⊗ₜ[D.ntw.O i]
      AddMonoidAlgebra.single (0 : DelQM D.host (D.ntw.l i) Q M) (1 : D.ntw.O i)
    twPsi := fun i j _ k _ => TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i k) (Pt D j → KK D i) 1
    twPsi_one := fun _ _ _ _ _ => rfl
    twDel := fun _ _ _ _ _ => 0
    thP := fun _ _ _ _ _ _ => 0
    hkF := fun i j _ => A i j
    embB := fun i j _ => intF D i j
    embB_inj := fun i j _ f g h => by
      funext y
      exact IsFractionRing.injective (D.ntw.O i) (KK D i) (congrFun h y)
    eH := fun _ _ _ => 1
    eH_idem := fun _ _ _ => mul_one _ }

theorem mem_intF (i : D.ntw.Tw) (j : ℕ) (f : Pt D j → KK D i) :
    f ∈ LinearMap.range (intF D i j) ↔ ∀ y, f y ∈ (algebraMap (D.ntw.O i) (KK D i)).range := by
  constructor
  · rintro ⟨g, rfl⟩ y
    exact ⟨g y, rfl⟩
  · intro h
    choose g hg using h
    exact ⟨g, funext hg⟩

open Classical in

@[reducible] def th : @NTh D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D) (ex D A s) :=
  { D.nth with
    Pt := fun _ j => Pt D j
    ev := fun i j _ => (D.nth.iC i).toAddMonoidHom.compLeft _
    ev_smul := fun i j _ a f y => map_mul (D.nth.iC i) a (f y)
    ev_inj := fun i j _ f g h => by
      funext y
      exact (D.nth.iC i).injective (congrFun h y)
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => (add_zero _).symm
    thV_smul := fun _ _ _ _ _ _ => (mul_zero _).symm
    thV_addP := fun _ _ _ _ _ _ => (add_zero _).symm
    thV_smulP := fun _ _ _ _ _ _ => (mul_zero _).symm
    datPhi := fun _ _ _ _ _ => 0
    datP := fun _ _ _ _ => 0
    recDet := fun _ _ _ => 1
    Kq := fun _ _ _ => PUnit
    grpKq := fun _ _ _ => inferInstance
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun _ j _ _ => Pt D j
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun _ _ _ _ c _ => c
    hkU := fun i j _ k P c y => D.nth.iC i (A i j k P (Pi.single c 1) y)
    hk_ev := fun i j _ k P _ _ _ _ f y => by
      change D.nth.iC i (A i j k P f y) = ∑ c, D.nth.iC i (A i j k P (Pi.single c 1) y) * D.nth.iC i (f c)
      simp_rw [← map_mul, ← map_sum]
      congr 1
      conv_lhs => rw [pi_eq_sum_univ' f]
      simp [map_sum, mul_comm]
    MaximalUnramifiedExtension := fun _ => ⊤
    FmUr := fun _ _ _ => ⊤
    FmUr_smul := fun _ _ _ _ _ _ _ => trivial
    FmUr_span := fun _ _ _ => by simp
    Bsup_def := fun i j _ => by
      have : {f : Pt D j → KK D i | f ∈ (⊤ : AddSubgroup (Pt D j → KK D i)) ∧ ∀ y, ‖D.nth.iC i (f y)‖ ≤ 1} =
          (LinearMap.range (intF D i j) : Set _) := by
        ext f
        simp only [AddSubgroup.mem_top, true_and, Set.mem_setOf_eq, SetLike.mem_coe, mem_intF, D.nth.iC_int]
      change LinearMap.range (intF D i j) = Submodule.span _
        {f : Pt D j → KK D i | f ∈ (⊤ : AddSubgroup (Pt D j → KK D i)) ∧ ∀ y, ‖D.nth.iC i (f y)‖ ≤ 1}
      rw [this, Submodule.span_eq] }

@[reducible] def rec : D7 := { D with ntw := tw D, nexp := ex D A s, nth := th D A s }

def dat : XD (rec D A s) where
  Dat0 := fun _ _ _ => Set.univ
  theta_base_equivariant := fun i j b a _ u => by
    have hu : (u : G0g D.nd) = 1 := Subgroup.mem_bot.1 u.2
    rw [hu]
    funext y
    simp [transl]

theorem inNonzeroPlaces_recursive_iff (i : D.ntw.Tw) : (rec D A s).ntw.NonzeroIndexPlace i ↔ D.ntw.NonzeroIndexPlace i := Iff.rfl

end GlobalTheory.SupLaw.Model

end
