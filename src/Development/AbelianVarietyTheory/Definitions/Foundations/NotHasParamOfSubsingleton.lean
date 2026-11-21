import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.LFun.Model

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

def constMap (G : Type) : ℂ →ₗ[ℂ] (G → ℂ) := LinearMap.pi fun _ => LinearMap.id

theorem constMap_injective (G : Type) [Group G] : Function.Injective (constMap G) := fun _ _ h => congrFun h 1

section Linear

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

def rhoGL (i : Fin n) : ℂˣ := npowU w (((n : ℂ) - 1) / 2 - (i : ℕ))

theorem chiDelta_rhoGL (b : GL (Fin n) (w.adicCompletion E)) : chiDelta E w (fun i => (rhoGL w n i : ℂ)) b = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
  change (((qV E w : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2 - (i : ℕ))) ^ _ * _ = 1
  rw [← Complex.cpow_mul_int, ← Complex.cpow_add _ _ hq]
  convert Complex.cpow_zero _ using 2
  ring

theorem hasSatGL_trivial : HasSatGL w (Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (seg w 1 n) := by
  have e : seg w 1 n = Finset.univ.val.map (rhoGL w n) := by
    rw [seg, Finset.range_val, ← Multiset.coe_range, ← List.map_coe_finRange_eq_range, Multiset.map_coe, List.map_map]
    simp only [one_mul]
    rfl
  rw [e]
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecGL.of_map (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecGL_of_isSpherical (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  rw [chiDelta_rhoGL, one_mul]; rfl

end Linear

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {ϖ : L} {q : ℕ}

def rhoU {q : ℕ} (hq : q ≠ 0) (n : ℕ) (i : Fin (n / 2)) : ℂˣ :=
  Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem hasSatU_trivial (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    HasSatU ϖ q (Representation.trivial ℂ (GU σ n) ℂ) (rhoU hq n) := by
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecU.of_map hU (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecU_of_isSphericalU hU (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  have : chiDeltaU q (fun i => (rhoU hq n i : ℂ)) b = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs
    · simp only [rhoU, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero _ using 2
      ring
    · rfl
  rw [this, one_mul]; rfl

end U

end GlobalTheory.LFun.Model

end
