import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameInvariantLevelAction
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

section Res

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def resI (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : Formalism.L2.Herm.intAf F E →+* 𝓞 E ⧸ I :=
  ((RingEquiv.ofBijective (cmpS F I) (cmpS_bij (F := F) I hI)).symm : _ →+* 𝓞 E ⧸ I).comp
    (Ideal.Quotient.mk (idS F I))

variable {F}

theorem resI_oToS (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (a : 𝓞 E) :
    resI F I hI (oToS F E a) = Ideal.Quotient.mk I a := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem resI_eq_zero_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    resI F I hI s = 0 ↔ s ∈ idS F I := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _ ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem resS_eq_resI (w : Pl E) : resS F w = resI F w.asIdeal w.ne_bot := rfl

end Res

section CRT

variable {E : Type} [Field E] [NumberField E] {I : Ideal (𝓞 E)} {Pg : Finset (Pl E)}

def crtHom (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) : 𝓞 E ⧸ I →+* ∀ w : ↥Pg, kP w.1 :=
  RingHom.pi fun w => Ideal.Quotient.factor (hle w)

theorem crtHom_bijective (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) :
    Function.Bijective (crtHom hle) := by
  classical
  have hc : Pairwise (fun v w : ↥Pg => IsCoprime v.1.asIdeal w.1.asIdeal) := fun v w h =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun e => h (Subtype.ext e))
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, hP, ← Finset.prod_coe_sort Pg,
      Ideal.prod_eq_iInf_of_pairwise_isCoprime (fun v _ w _ h => hc h)]
    simp only [Finset.mem_univ, iInf_pos, Ideal.mem_iInf]
    intro w
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hx w)
  · intro x
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hc x
    exact ⟨Ideal.Quotient.mk I a, funext fun w => ha w⟩

def crt (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) : (𝓞 E ⧸ I) ≃+* ∀ w : ↥Pg, kP w.1 :=
  RingEquiv.ofBijective (crtHom hle) (crtHom_bijective hP hle)

theorem crt_apply (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) (x : 𝓞 E ⧸ I) (w : ↥Pg) :
    crt hP hle x w = Ideal.Quotient.factor (hle w) x := rfl

end CRT

end GlobalTheory.GeoActCompare
