import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonLift
import GroundTheory.PAdicHodge.PhiGammaBase
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
import GroundTheory.PAdicHodge.ExtRobbaBounded
import GroundTheory.PAdicHodge.ExtRobbaFixedTerm
import GroundTheory.PAdicHodge.ExtRobbaFixedSum
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne
import GroundTheory.PAdicHodge.ExtRobbaIsoLift
import GroundTheory.PAdicHodge.ExtRobbaTrivialSB
import GroundTheory.PAdicHodge.BCrisEigenWitt

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector

section Frob

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p

theorem incl_frobeniusEquiv (x : AInf K p) :
    incl K p (WittVector.frobeniusEquiv p 𝒪♭ x) = WittVector.frobeniusEquiv p K♭ (incl K p x) := by
  ext n
  rw [incl_coeff, WittVector.frobeniusEquiv_coeff, WittVector.frobeniusEquiv_coeff, incl_coeff,
    map_pow]

theorem incl_frobeniusEquiv_symm (x : AInf K p) :
    incl K p ((WittVector.frobeniusEquiv p 𝒪♭).symm x) =
      (WittVector.frobeniusEquiv p K♭).symm (incl K p x) := by
  apply (WittVector.frobeniusEquiv p K♭).injective
  rw [RingEquiv.apply_symm_apply, ← incl_frobeniusEquiv, RingEquiv.apply_symm_apply]

variable (K p) in

def frob : (teichLift K p).TeichFrob where
  φ := WittVector.frobeniusEquiv p K♭
  a := 1
  red_φ x := by
    show (WittVector.frobeniusEquiv p K♭ x).coeff 0 = x.coeff 0 ^ p ^ 1
    rw [WittVector.frobeniusEquiv_coeff, pow_one]
  u := 1
  φ_π := by
    rw [mul_one]
    exact map_natCast (WittVector.frobeniusEquiv p K♭) p
  u_mem_int := one_mem _
  norm_red_u := by
    show ‖(1 : WittVector p K♭).coeff 0‖ = 1
    rw [WittVector.one_coeff_zero, norm_one]
  map_int := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, incl_frobeniusEquiv y⟩
  symm_map_int := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, incl_frobeniusEquiv_symm y⟩

@[simp] theorem frob_a : (frob K p).a = 1 := rfl

@[simp] theorem frob_u : (frob K p).u = 1 := rfl

theorem coeff_frob (x : WittVector p K♭) (n : ℕ) :
    (teichLift K p).coeff ((frob K p).φ x) n = (teichLift K p).coeff x n ^ p := by
  set T := teichLift K p
  set F := frob K p
  have hred : ∀ y, T.red (F.φ.toRingHom y) = frobenius K♭ p (T.red y) := fun y => by
    rw [frobenius_def]
    have := F.red_φ y
    rw [frob_a, pow_one] at this
    exact this
  have hπ : F.φ.toRingHom T.π = T.π * 1 := F.φ_π
  have h1 := T.map_partialSum F.φ.toRingHom (frobenius K♭ p) hred hπ x (n + 1)
  have h2 := T.map_sub_map_partialSum_mem F.φ.toRingHom hπ x (n + 1)
  refine (T.coeff_eq_of_mem (a := fun m => frobenius K♭ p (T.coeff x m)) ?_ n le_rfl).trans
    (by rw [frobenius_def])
  have e : T.finSum (fun m => frobenius K♭ p (T.coeff x m)) (n + 1) =
      F.φ.toRingHom (T.partialSum x (n + 1)) := by
    rw [h1]; simp [TeichLift.finSum]
  rw [e]; exact h2

end Frob

section Galois

open PhiGamma

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

def galTiltEquiv (σ : Gal(PadicAlgCl p/K)) : Cb p ≃+* Cb p :=
  RingEquiv.ofRingHom (galTilt σ) (galTilt σ⁻¹)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← galTilt_mul, mul_inv_cancel, galTilt_one, RingHom.id_apply])
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← galTilt_mul, inv_mul_cancel, galTilt_one, RingHom.id_apply])

def galWEquiv (σ : Gal(PadicAlgCl p/K)) : WC p ≃+* WC p :=
  RingEquiv.ofRingHom (galW σ) (galW σ⁻¹)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← galW_mul, mul_inv_cancel, galW_one, RingHom.id_apply])
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← galW_mul, inv_mul_cancel, galW_one, RingHom.id_apply])

def galIso (σ : Gal(PadicAlgCl p/K)) : (teichLift ℂ_[p] p).TeichIso where
  ψ := galWEquiv σ
  g := galTiltEquiv σ
  red_ψ x := galW_coeff σ x 0
  ψ_π := gal_smul_natCast σ p
  norm_g c := norm_galTilt σ c

end Galois

section Unramified

open PhiGamma EigenWitt

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝓣" => teichLift ℂ_[p] p
local notation "W̄" => WittVector p (Fpbar p)

variable (p) in

abbrev WFrac : Type := FractionRing (WittVector p (Fpbar p))

variable (p) in

def wittFpbarToWC : W̄ →+* WC p := (incl ℂ_[p] p).comp wittToAInf

theorem wittFpbarToWC_mem_int (w : W̄) : wittFpbarToWC p w ∈ (𝓣).int := ⟨_, rfl⟩

theorem exists_eq_zpow_mul (x : WFrac p) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : W̄ˣ), x = (algebraMap W̄ (WFrac p) p) ^ n * algebraMap W̄ (WFrac p) u := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := W̄) x
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  have hs : s ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨m, ua, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
  obtain ⟨k, us, rfl⟩ := WittVector.exists_eq_pow_p_mul' s hs
  refine ⟨(m : ℤ) - k, ua * us⁻¹, ?_⟩
  have hp0 : algebraMap W̄ (WFrac p) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W̄ (WFrac p))).2 (WittVector.irreducible p).ne_zero
  have hus : algebraMap W̄ (WFrac p) (us : W̄) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W̄ (WFrac p))).2 us.ne_zero
  rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast, Units.val_mul, map_mul, map_mul, map_mul, map_pow,
    map_pow]
  have : algebraMap W̄ (WFrac p) ((us⁻¹ : W̄ˣ) : W̄) = (algebraMap W̄ (WFrac p) (us : W̄))⁻¹ :=
    map_units_inv _ us
  rw [this]
  field_simp

theorem isUnit_wittFpbar_to_B (y : nonZeroDivisors W̄) :
    IsUnit ((algebraMap (WC p) (𝓣).B).comp (wittFpbarToWC p) y) := by
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (y : W̄) (nonZeroDivisors.coe_ne_zero y)
  have hf : (algebraMap (WC p) (𝓣).B).comp (wittFpbarToWC p) (p : W̄) =
      algebraMap (WC p) (𝓣).B (𝓣).π := by
    rw [RingHom.comp_apply, map_natCast]; rfl
  rw [hu, map_mul, map_pow, hf]
  exact IsUnit.mul (IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit (𝓣).π)) (u.isUnit.map _)

variable (p) in

def wittFpbarToB : WFrac p →+* (𝓣).B :=
  IsLocalization.lift (M := nonZeroDivisors W̄) (isUnit_wittFpbar_to_B (p := p))

theorem wittFpbarToB_algebraMap (w : W̄) :
    wittFpbarToB p (algebraMap W̄ (WFrac p) w) = algebraMap (WC p) (𝓣).B (wittFpbarToWC p w) :=
  IsLocalization.lift_eq _ w

theorem wittFpbarToB_p : wittFpbarToB p (algebraMap W̄ (WFrac p) p) = (𝓣).πB := by
  rw [wittFpbarToB_algebraMap, map_natCast]; rfl

end Unramified

section Tilde

open PhiGamma EigenWitt

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "W̄" => WittVector p (Fpbar p)

theorem convAll_piB_zpow (n : ℤ) : (𝓣).ConvAll ((((𝓣).piB ^ n : ((𝓣).B)ˣ)) : (𝓣).B) := by
  have hpow : ∀ (b : (𝓣).B), (𝓣).ConvAll b → ∀ k : ℕ, (𝓣).ConvAll (b ^ k) := by
    intro b hb k
    induction k with
    | zero => rw [pow_zero]; simpa using (TeichLift.convAll_π_pow (T := 𝓣) 0)
    | succ k ih => rw [pow_succ]; exact ih.mul hb
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, TeichLift.piB_val]
    exact TeichLift.convAll_π_pow k
  · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have : (((𝓣).piB⁻¹ : ((𝓣).B)ˣ) : (𝓣).B) = IsLocalization.Away.invSelf (𝓣).π :=
      Units.inv_eq_of_mul_eq_one_right (by rw [TeichLift.piB_val]; exact IsLocalization.Away.mul_invSelf _)
    rw [this]
    exact hpow _ TeichLift.convAll_invSelf _

theorem wittFpbarToB_zpow_mul (n : ℤ) (w : W̄) :
    wittFpbarToB p ((algebraMap W̄ (WFrac p) p) ^ n * algebraMap W̄ (WFrac p) w) =
      (((𝓣).piB ^ n : ((𝓣).B)ˣ) : (𝓣).B) * algebraMap (WC p) (𝓣).B (wittFpbarToWC p w) := by
  have hP : IsUnit (algebraMap W̄ (WFrac p) p) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective W̄ (WFrac p))).2
      (WittVector.irreducible p).ne_zero).isUnit
  have e1 : (algebraMap W̄ (WFrac p) p) ^ n = ((hP.unit ^ n : (WFrac p)ˣ) : WFrac p) := by
    rw [Units.val_zpow_eq_zpow_val, IsUnit.unit_spec]
  have e2 : Units.map (wittFpbarToB p : WFrac p →* (𝓣).B) hP.unit = (𝓣).piB := by
    ext
    rw [Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, wittFpbarToB_p, TeichLift.piB_val]
  rw [map_mul, e1, wittFpbarToB_algebraMap, ← e2, ← map_zpow, Units.coe_map, MonoidHom.coe_coe]

theorem convAll_wittFpbarToB (x : WFrac p) : (𝓣).ConvAll (wittFpbarToB p x) := by
  by_cases hx : x = 0
  · rw [hx, map_zero]; exact TeichLift.convAll_zero
  obtain ⟨n, u, rfl⟩ := exists_eq_zpow_mul x hx
  rw [wittFpbarToB_zpow_mul]
  exact (convAll_piB_zpow n).mul
    (TeichLift.convAll_algebraMap_of_mem_int (wittFpbarToWC_mem_int (u : W̄)))

theorem wittFpbarToB_mem_Edag (x : WFrac p) : wittFpbarToB p x ∈ (𝓣).Edag :=
  (𝓣).Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩ (convAll_wittFpbarToB x _ (by norm_num) (by norm_num))

variable (p) in

def wittFpbarToEdag : WFrac p →+* (𝓣).Edag :=
  (wittFpbarToB p).codRestrict _ wittFpbarToB_mem_Edag

variable (p) in

def wittFpbarToTilde : WFrac p →+* (𝓣).RobbaTilde := (𝓣).edagToTilde.comp (wittFpbarToEdag p)

end Tilde

end WittTilt

end GroundTheory.PAdicHodge
