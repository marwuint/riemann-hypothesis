import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers

noncomputable section

namespace GlobalTheory.EX.DQ.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB NumberField

theorem tup_setDiv (D : D7) (N) (h) : TupUsedAt (setDiv D N h) ↔ TupUsedAt D := Iff.rfl
theorem mt_setDiv (D : D7) (N) (h) : MtStableAt (setDiv D N h) ↔ MtStableAt D := Iff.rfl
theorem conj_setDiv (D : D7) (O : Obj D) (N) (h) : TwConjAt (setDiv D N h) (O.tr N h).nch ↔ TwConjAt D O.nch := Iff.rfl
theorem av_setDiv (D : D7) (N) (h) : AvRec (setDiv D N h) = AvRec D := rfl
theorem ok_setDiv (D : D7) (N) (h) (I : TwIn D) (i) : TwIn.Ok (D := setDiv D N h) ⟨{I.E with}, I.N0, I.S⟩ i ↔ I.Ok i := Iff.rfl
set_option maxHeartbeats 2000000 in
theorem one_setDiv (D : D7) (N) (h) (I : TwIn D) (i b Q k ψ) : TwGoodOne (setDiv D N h) ⟨{I.E with}, I.N0, I.S⟩ i b Q k ψ ↔ TwGoodOne D I i b Q k ψ := Iff.rfl

section Lat

variable {O L V : Type} [CommRing O] [Field L] [NumberField L] [AddCommGroup V] [Module ℂ V] {φ : O →+* ℂ}

open Classical in

def sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) : Rows.OLat O φ V where
  gen := (Finset.univ ×ˢ M.gen).image fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2
  span_top := by
    rw [eq_top_iff, ← M.span_top, Submodule.span_le]
    intro v hv
    obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 L)) := (RingOfIntegers.basis L).index_nonempty
    have h0 : σ (RingOfIntegers.basis L i : L) ≠ 0 := by
      rw [map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
      exact (RingOfIntegers.basis L).ne_zero i
    have := Submodule.smul_mem (Submodule.span ℂ (((Finset.univ ×ˢ M.gen).image
      fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2 : Finset V) : Set V)) (σ (RingOfIntegers.basis L i : L))⁻¹
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, v), by simpa using hv, rfl⟩)))
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this

end Lat

set_option maxHeartbeats 4000000 in

def setMt (D : D7) (M : ∀ μ, Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (D.what₂.Amb μ)) : D7 :=
  { D with
    what₂ := { D.what₂ with Mtilde := M }
    nd := { D.nd with }
    ntw := { D.ntw with }
    naut := { D.naut with }
    nbc := { D.nbc with }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with }
    nth := { D.nth with } }

theorem tup_setMt (D : D7) (M) : TupUsedAt (setMt D M) ↔ TupUsedAt D := Iff.rfl

end GlobalTheory.EX.DQ.Model

end
