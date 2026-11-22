import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import GroundTheory.LocalFields.FormalGroups.LubinTateGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIsEval
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKReal GlobalTheory.Prism IsLocalRing Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.DiscEval
open GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per TensorProduct

namespace GlobalTheory.AcrisK

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

variable (l) in

abbrev aC : Ainf l →+* Per.Acris l := algebraMap (Per.Ainf l) (Per.Acris l)

scoped instance algWC : Algebra (W0 K) (Per.Acris l) := ((aC l).comp (wA l (fK K)).toRingHom).toAlgebra

def CK : Type := Per.Acris l ⊗[W0 K] ↥(OL K)

instance : CommRing (CK K) := inferInstanceAs (CommRing (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Algebra (Per.Acris l) (CK K) :=
  inferInstanceAs (Algebra (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Algebra ↥(OL K) (CK K) :=
  (Algebra.TensorProduct.includeRight : ↥(OL K) →ₐ[W0 K] Per.Acris l ⊗[W0 K] ↥(OL K)).toRingHom.toAlgebra

instance : Module.Free (Per.Acris l) (CK K) :=
  inferInstanceAs (Module.Free (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

instance : Module.Finite (Per.Acris l) (CK K) :=
  inferInstanceAs (Module.Finite (Per.Acris l) (Per.Acris l ⊗[W0 K] ↥(OL K)))

abbrev inC : Per.Acris l →+* CK K := algebraMap (Per.Acris l) (CK K)

abbrev inI : ↥(OL K) →+* CK K := algebraMap ↥(OL K) (CK K)

theorem tmul_eq (a : Per.Acris l) (c : ↥(OL K)) : (show CK K from a ⊗ₜ[W0 K] c) = inC K a * inI K c := by
  change a ⊗ₜ[W0 K] c = (a ⊗ₜ[W0 K] (1 : ↥(OL K))) * ((1 : Per.Acris l) ⊗ₜ[W0 K] c)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem inC_wA (w : W0 K) : inC K (aC l (wA l (fK K) w)) = inI K (thetaW (fK K) K w) :=
  ((Algebra.TensorProduct.includeRight : ↥(OL K) →ₐ[W0 K] Per.Acris l ⊗[W0 K] ↥(OL K)).commutes w).symm

variable {K} in

@[elab_as_elim] theorem induction_on {p : CK K → Prop} (x : CK K) (mul : ∀ a c, p (inC K a * inI K c))
    (add : ∀ x y, p x → p y → p (x + y)) : p x :=
  TensorProduct.induction_on (motive := p) x (by
    have := mul 0 0; rwa [map_zero, zero_mul] at this) (fun a c => by
    have := mul a c; rwa [← tmul_eq] at this) add

variable {K} in

theorem ringHom_ext {S : Type*} [CommRing S] {u v : CK K →+* S} (hA : ∀ a, u (inC K a) = v (inC K a))
    (hO : ∀ c, u (inI K c) = v (inI K c)) : u = v :=
  RingHom.ext fun x => induction_on x (fun a c => by rw [map_mul, map_mul, hA, hO])
    fun x y hx hy => by rw [map_add, map_add, hx, hy]

section Lift

variable {K} {S : Type*} [CommRing S] (u : Per.Acris l →+* S) (v : ↥(OL K) →+* S)
  (h : ∀ w : W0 K, u (aC l (wA l (fK K) w)) = v (thetaW (fK K) K w))

def lift : CK K →+* S :=
  letI : Algebra (W0 K) S := (u.comp ((aC l).comp (wA l (fK K)).toRingHom)).toAlgebra
  (Algebra.TensorProduct.productMap (R := W0 K) { toRingHom := u, commutes' := fun _ => rfl }
    { toRingHom := v, commutes' := fun w => (h w).symm }).toRingHom

@[simp] theorem lift_inC (a : Per.Acris l) : lift u v h (inC K a) = u a := by
  change u a * v 1 = u a
  rw [map_one, mul_one]

@[simp] theorem lift_inI (c : ↥(OL K)) : lift u v h (inI K c) = v c := by
  change u 1 * v c = v c
  rw [map_one, one_mul]

end Lift

def ofA : AK K →+* CK K := AinfK.lift ((inC K).comp (aC l)) (inI K) (inC_wA K)

theorem ofA_inA (a : Ainf l) : ofA K (inA K a) = inC K (aC l a) := lift_inA _ _ _ a

theorem ofA_inO (c : ↥(OL K)) : ofA K (inO K c) = inI K c := lift_inO _ _ _ c

instance complete_l : IsAdicComplete (Ideal.span {(l : CK K)}) (CK K) := by
  have h := GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis (W0 K) ↥(OL K)) (l : Per.Acris l)
    (h := (acris_basic l).1)
  let e : ↥(OL K) ⊗[W0 K] Per.Acris l ≃+* CK K :=
    (Algebra.TensorProduct.comm (W0 K) ↥(OL K) (Per.Acris l)).toRingEquiv
  rw [← IsAdicComplete.congr_ringEquiv _ e, Ideal.map_span, Set.image_singleton] at h
  have e1 : e ((1 : ↥(OL K)) ⊗ₜ[W0 K] (l : Per.Acris l)) = (l : CK K) := map_natCast (inC K) l
  rwa [e1] at h

variable {K} in

theorem eq_zero_of_l_mul {x : CK K} (h : (l : CK K) * x = 0) : x = 0 := by
  rw [← map_natCast (inC K), ← Algebra.smul_def] at h
  refine (Module.Free.chooseBasis (Per.Acris l) (CK K)).repr.injective (Finsupp.ext fun i => ?_)
  have h1 := congrArg (fun y => (Module.Free.chooseBasis (Per.Acris l) (CK K)).repr y i) h
  simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h1 ⊢
  exact (acris_basic l).2.1 _ h1

variable {K}

theorem sigA_aC (g : GQ l) (a : Ainf l) : sigA g (aC l a) = aC l (Per.σA g a) := (GlobalTheory.CrisMaps.sigA_extends g).alg a

def galC (g : ↥(GK K)) : CK K →+* CK K :=
  lift ((inC K).comp (sigA (g : GQ l))) (inI K) fun w => by
    rw [RingHom.comp_apply, sigA_aC, σA_wA, inC_wA]

theorem galC_inC (g : ↥(GK K)) (a : Per.Acris l) : galC g (inC K a) = inC K (sigA (g : GQ l) a) :=
  lift_inC _ _ _ a

theorem galC_inI (g : ↥(GK K)) (c : ↥(OL K)) : galC g (inI K c) = inI K c := lift_inI _ _ _ c

theorem galC_ofA (g : ↥(GK K)) (x : AK K) : galC g (ofA K x) = ofA K (gal K g x) :=
  AinfK.induction_on x (fun a c => by
    simp only [map_mul, ofA_inA, ofA_inO, galC_inC, galC_inI, gal_inA, gal_inO, sigA_aC])
    fun x y hx hy => by simp only [map_add, hx, hy]

variable (K)

def BK : Type := Localization.Away (l : CK K)

instance : CommRing (BK K) := inferInstanceAs (CommRing (Localization.Away (l : CK K)))

instance : Algebra (CK K) (BK K) := inferInstanceAs (Algebra (CK K) (Localization.Away (l : CK K)))

instance : IsLocalization.Away (l : CK K) (BK K) :=
  inferInstanceAs (IsLocalization.Away _ (Localization.Away (l : CK K)))

abbrev toB : CK K →+* BK K := algebraMap (CK K) (BK K)

theorem isUnit_l : IsUnit (l : BK K) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := BK K) (l : CK K)
  rwa [map_natCast] at h

theorem toB_injective : Function.Injective (toB K) :=
  IsLocalization.injective (M := Submonoid.powers (l : CK K)) (BK K) (Submonoid.powers_le.2
    (mem_nonZeroDivisors_iff_left.2 fun _ h => eq_zero_of_l_mul h))

variable {K} in

theorem isUnit_map {S : Type*} [CommRing S] (hS : IsUnit (l : S)) (v : ↥(OL K) →+* S)
    (c : nonZeroDivisors ↥(OL K)) : IsUnit (v c) := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.coe_ne_zero c) hπ
  have h1 := map_dvd v (h.dvd.trans (pow_dvd_pow_of_dvd (dvd_of_not_isUnit hπ (l_mem_max K)) n))
  rw [map_pow, map_natCast] at h1
  exact isUnit_of_dvd_unit h1 (hS.pow n)

abbrev oK : ↥(OL K) →+* ↥K.1 := algebraMap ↥(OL K) ↥K.1

def inK : ↥K.1 →+* BK K :=
  IsLocalization.lift (M := nonZeroDivisors ↥(OL K)) (g := (toB K).comp (inI K)) (isUnit_map (isUnit_l K) _)

theorem inK_oK (c : ↥(OL K)) : inK K (oK K c) = toB K (inI K c) := IsLocalization.lift_eq _ c

def inP : BcrisP l →+* BK K := plusLift ((toB K).comp (inC K)) (isUnit_l K)

variable {K}

theorem ringHom_extK {S : Type*} [CommRing S] {u v : ↥K.1 →+* S} (h : ∀ c, u (oK K c) = v (oK K c)) : u = v :=
  IsLocalization.ringHom_ext (nonZeroDivisors ↥(OL K)) (RingHom.ext h)

def awayLift {S : Type*} [CommRing S] (f : CK K →+* S) (h : IsUnit (l : S)) : BK K →+* S :=
  IsLocalization.Away.lift (l : CK K) (g := f) (by rwa [map_natCast])

theorem awayLift_toB {S : Type*} [CommRing S] (f : CK K →+* S) (h : IsUnit (l : S)) (z : CK K) :
    awayLift f h (toB K z) = f z := IsLocalization.Away.lift_eq _ _ z

theorem awayLift_inK (s : CK K →+* CK K) (hs : ∀ c, s (inI K c) = inI K c) (c : ↥K.1) :
    awayLift ((toB K).comp s) (isUnit_l K) (inK K c) = inK K c :=
  RingHom.congr_fun (ringHom_extK (u := (awayLift ((toB K).comp s) (isUnit_l K)).comp (inK K)) (v := inK K)
    fun c => by rw [RingHom.comp_apply, inK_oK, awayLift_toB, RingHom.comp_apply, hs]) c

def galB (g : ↥(GK K)) : BK K →+* BK K := awayLift ((toB K).comp (galC g)) (isUnit_l K)

theorem galB_toB (g : ↥(GK K)) (z : CK K) : galB g (toB K z) = toB K (galC g z) := awayLift_toB _ _ z

theorem galB_inK (g : ↥(GK K)) (c : ↥K.1) : galB g (inK K c) = inK K c := awayLift_inK _ (galC_inI g) c

variable (K)

scoped instance algWP : Algebra (W0 K) (BcrisP l) :=
  ((algebraMap (Per.Acris l) (BcrisP l)).comp ((aC l).comp (wA l (fK K)).toRingHom)).toAlgebra

scoped instance algWK : Algebra (W0 K) ↥K.1 := ((oK K).comp (thetaW (fK K) K).toRingHom).toAlgebra

abbrev PK : Type := BcrisP l ⊗[W0 K] ↥K.1

variable {K}

def Ev (L : PowerSeries ↥K.1) (x : AK K) (y : BK K) : Prop := IsEval l (toB K) (inK K) L (toB K (ofA K x)) y

theorem Ev.unique {L : PowerSeries ↥K.1} {x : AK K} {y y' : BK K} (h : Ev L x y) (h' : Ev L x y') : y = y' :=
  Tends.unique (toB_injective K) h h'

theorem Ev.gal (g : ↥(GK K)) {L : PowerSeries ↥K.1} {x : AK K} {y : BK K} (h : Ev L x y) :
    Ev L (gal K g x) (galB g y) := by
  have := IsEval.map (i' := toB K) (κ' := inK K) (galB g) (RingHom.id _) (fun z => ⟨_, galB_toB g z⟩) (galB_inK g) h
  rwa [PowerSeries.map_id, galB_toB, galC_ofA] at this

end GlobalTheory.AcrisK
