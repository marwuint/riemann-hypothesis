import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.Cyc

variable (l : ℕ) [Fact l.Prime]

section Rings₀

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def cyc (c : ℤ_[l]) : PowerSeries O :=
  PowerSeries.map (algebraMap ℤ_[l] O) (PowerSeries.binomialSeries ℤ_[l] c) - 1

theorem cyc_const (c : ℤ_[l]) : PowerSeries.constantCoeff (cyc l O c) = 0 := by
  rw [cyc, map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.binomialSeries_coeff]
  simp

def act (c : ℤ_[l]) : PowerSeries O →ₐ[O] PowerSeries O :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (cyc_const l O c))

def phi : PowerSeries O →ₐ[O] PowerSeries O := act l O (l : ℤ_[l])

def XX (s : ℕ) : PowerSeries O := (1 + PowerSeries.X) ^ l ^ (s - 1) - 1

def QQ (s : ℕ) : PowerSeries O := ∑ k ∈ Finset.range l, (1 + XX l O s) ^ k

namespace Series

theorem cyc_eq (c : ℤ_[l]) : cyc l O c = PowerSeries.binomialSeries O c - 1 := by
  rw [cyc, Fon.map_binomialSeries _ (fun _ => rfl)]

theorem act_X (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := PowerSeries.substAlgHom_X _

theorem act_eq (c : ℤ_[l]) : act l O c = Fon.gam O c :=
  Fon.algHom_ext_X (by rw [act_X, cyc_eq, Fon.gam_X]) (by rw [act_X, cyc_const])

theorem phi_eq : phi l O = Fon.phi0 l O := by rw [phi, act_eq, Fon.gam_l]

theorem phi_X : phi l O PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 := by rw [phi_eq, Fon.cyclotomicFrobeniusPowerSeries_X]

theorem phi_pow_X (s : ℕ) : (phi l O ^ (s - 1)) PowerSeries.X = XX l O s := by
  rw [phi_eq, Fon.cyclotomicFrobeniusPowerSeries_pow_apply_X, XX]

theorem phi_XX (s : ℕ) : phi l O (XX l O s) = XX l O s * QQ l O s := by
  rw [phi_eq]; exact Fon.cyclotomicFrobenius_iteratedVariable_eq_mul l O s

theorem phi_X_mod : ∃ r, phi l O PowerSeries.X = PowerSeries.X ^ l + (l : PowerSeries O) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (1 : PowerSeries O) PowerSeries.X
  exact ⟨PowerSeries.X * r, by rw [phi_X, hr]; ring⟩

end Series

def EE (n : ℕ) : Type :=
  AdicCompletion (Ideal.span {((l : ℕ) : Localization.Away (letπ : LetA O n))})
    (Localization.Away (letπ : LetA O n))

instance (n : ℕ) : CommRing (EE l O n) :=
  inferInstanceAs (CommRing (AdicCompletion (Ideal.span {((l : ℕ) : Localization.Away (letπ : LetA O n))})
    (Localization.Away (letπ : LetA O n))))

instance (n : ℕ) : Algebra (Localization.Away (letπ : LetA O n)) (EE l O n) :=
  inferInstanceAs (Algebra (Localization.Away (letπ : LetA O n))
    (AdicCompletion (Ideal.span {((l : ℕ) : Localization.Away (letπ : LetA O n))})
      (Localization.Away (letπ : LetA O n))))

def toEE (n : ℕ) : LetA O n →+* EE l O n :=
  (algebraMap (Localization.Away (letπ : LetA O n)) (EE l O n)).comp (algebraMap (LetA O n) _)

instance (n : ℕ) : Algebra (LetA O n) (EE l O n) := (toEE l O n).toAlgebra

instance (n : ℕ) : Algebra O (EE l O n) := ((toEE l O n).comp (algebraMap O (LetA O n))).toAlgebra

instance (n : ℕ) : IsScalarTower O (LetA O n) (EE l O n) := IsScalarTower.of_algebraMap_eq fun _ => rfl

namespace Completion

open Series

variable (n : ℕ)

instance lComplete_EE : Fon.LComplete l (EE l O n) := by
  have h := (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {(l : Localization.Away (letπ : LetA O n))}) (Localization.Away (letπ : LetA O n)))
    (Ideal.span {(l : Localization.Away (letπ : LetA O n))})
    (AdicCompletion (Ideal.span {(l : Localization.Away (letπ : LetA O n))}) (Localization.Away (letπ : LetA O n)))).2
    (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _))
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

variable {l O n}

def liftEE {B : Type} [CommRing B] [Fon.LComplete l B] (f : LetA O n →+* B) (hf : IsUnit (f letπ)) :
    EE l O n →+* B :=
  ((AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm : _ →+* B).comp
    (GlobalTheory.AdicMaps.padicMap l (IsLocalization.Away.lift (S := Localization.Away (letπ : LetA O n)) letπ hf))

omit [Algebra ℤ_[l] O] in

@[simp] theorem liftEE_toEE {B : Type} [CommRing B] [Fon.LComplete l B] (f : LetA O n →+* B)
    (hf : IsUnit (f letπ)) (a : LetA O n) : liftEE (l := l) f hf (toEE l O n a) = f a := by
  have h := GlobalTheory.AdicMaps.padicMap_alg l
    (IsLocalization.Away.lift (S := Localization.Away (letπ : LetA O n)) letπ hf) (algebraMap _ _ a)
  rw [IsLocalization.Away.lift_eq] at h
  exact (congrArg (AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm h).trans
    ((AdicCompletion.ofAlgEquiv (Ideal.span {(l : B)})).symm.commutes _)

def extEE (f : LetA O n →ₐ[O] LetA O n) (hf : IsUnit (toEE l O n (f letπ))) : EE l O n →ₐ[O] EE l O n where
  toRingHom := liftEE ((toEE l O n).comp (f : LetA O n →+* LetA O n)) hf
  commutes' r := (liftEE_toEE _ hf (algebraMap O (LetA O n) r)).trans
    (congrArg (toEE l O n) (f.commutes r))

omit [Algebra ℤ_[l] O] in

@[simp] theorem extEE_toEE (f : LetA O n →ₐ[O] LetA O n) (hf : IsUnit (toEE l O n (f letπ))) (a : LetA O n) :
    extEE f hf (toEE l O n a) = toEE l O n (f a) := liftEE_toEE _ hf a

variable (l O n)

end Completion

end Rings₀

open Series Completion

def clW (S : Set (WCb l)) : Set (WCb l) :=
  {x | ∀ k : ℕ, ∃ y ∈ S, x - y ∈ Ideal.span {((l : ℕ) : WCb l) ^ k}}

variable {l}

theorem mem_clW {S : Set (WCb l)} {x : WCb l} :
    x ∈ clW l S ↔ ∀ k : ℕ, ∃ y ∈ S, (l : WCb l) ^ k ∣ x - y := by
  simp only [clW, Set.mem_setOf_eq, Ideal.mem_span_singleton]

def clAlg (S : Subalgebra ℤ_[l] (WCb l)) : Subalgebra ℤ_[l] (WCb l) where
  carrier := clW l S
  add_mem' {a b} ha hb := mem_clW.2 fun k => by
    obtain ⟨x, hx, h⟩ := mem_clW.1 ha k
    obtain ⟨y, hy, h'⟩ := mem_clW.1 hb k
    exact ⟨x + y, S.add_mem hx hy, by convert h.add h' using 1; ring⟩
  mul_mem' {a b} ha hb := mem_clW.2 fun k => by
    obtain ⟨x, hx, h⟩ := mem_clW.1 ha k
    obtain ⟨y, hy, h'⟩ := mem_clW.1 hb k
    exact ⟨x * y, S.mul_mem hx hy, by convert (h.mul_right b).add (h'.mul_left x) using 1; ring⟩
  algebraMap_mem' z := mem_clW.2 fun _ => ⟨_, S.algebraMap_mem z, by simp⟩

def IsIo (e : OCb l) (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l) : Prop :=
  io PowerSeries.X = WittVector.teichmuller l e - 1

theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [← ih, pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p,
      LocAinf.εroot]

theorem εroot_sub_one_not_unit {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : ¬ IsUnit (AI.εroot s - 1) := by
  intro h
  have h1 := (h.pow (l ^ s)).map (PreTilt.coeff 0)
  rw [sub_pow_char_pow, εroot_pow, one_pow, map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one, sub_self] at h1
  haveI : Nontrivial (ModP (OC l) l) := CharP.nontrivial_of_char_ne_one (Fact.out : l.Prime).ne_one
  exact not_isUnit_zero h1

section Rings

variable (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l)

def E0loc : Subalgebra ℤ_[l] (WCb l) where
  carrier := {x | ∃ (a : PowerSeries ℤ_[l]) (m : ℕ), x * inclW l (io PowerSeries.X) ^ m = inclW l (io a)}
  add_mem' := by
    rintro x y ⟨a, m, h⟩ ⟨b, n, h'⟩
    refine ⟨a * PowerSeries.X ^ n + b * PowerSeries.X ^ m, m + n, ?_⟩
    simp only [map_add, map_mul, map_pow, ← h, ← h']
    ring
  mul_mem' := by
    rintro x y ⟨a, m, h⟩ ⟨b, n, h'⟩
    refine ⟨a * b, m + n, ?_⟩
    simp only [map_mul, ← h, ← h']
    ring
  algebraMap_mem' z := ⟨algebraMap _ _ z, 0, by
    rw [pow_zero, mul_one, io.commutes]; exact ((inclWA l).commutes z).symm⟩

def E0 : Subalgebra ℤ_[l] (WCb l) := clAlg (E0loc io)

def simpleRoots : Set (WCb l) :=
  {y | ∃ f : Polynomial (WCb l), f.Monic ∧ (∀ i, f.coeff i ∈ E0 io) ∧ f.eval y = 0 ∧
    IsUnit (f.derivative.eval y)}

def EurAlg : Subalgebra ℤ_[l] (WCb l) := Algebra.adjoin ℤ_[l] (simpleRoots io)

def Eur : Subalgebra ℤ_[l] (WCb l) := clAlg (EurAlg io)

variable {io}

variable (io)

end Rings

section Module

@[reducible] def leftModuleGen (O R M : Type) [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] : Module R (R ⊗[O] M) := inferInstance

@[reducible] def leftSMulGen (O R M : Type) [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] : SMul R (R ⊗[O] M) := inferInstance

variable {G : Type} [Group G] [TopologicalSpace G]

scoped instance smulTW (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : SMul (RW LL) (TW (RW LL) T) :=
  leftSMulGen _ _ _

scoped instance moduleTW (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    Module (RW LL) (TW (RW LL) T) :=
  leftModuleGen _ _ _

def EurT (LL : FinExt l) (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    Submodule ↥(OL LL) (TW (RW LL) T) :=
  Submodule.span ↥(OL LL) {z | ∃ w ∈ Eur io, ∃ t : ↥T.L.T,
    z = ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) ⊗ₜ[↥(OL LL)] t}

variable {LL : FinExt l} {io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l} {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)}

end Module

def FonD {P : LocPrime l} (AI : LocAinf l P) (K LL : FinExt l)
    (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) :
    Submodule ↥(OL LL) (TW (RW LL) T) :=
  EurT LL io T ⊓ ⨅ g : {g : ↥(GK K) // P.χQ (g : GQ l) = 1},
    LinearMap.eqLocus (TWact (AI.gRW LL (g.1 : GQ l)) T g.1)
      (LinearMap.id : TW (RW LL) T →ₗ[↥(OL LL)] TW (RW LL) T)

end GlobalTheory.Cyc
