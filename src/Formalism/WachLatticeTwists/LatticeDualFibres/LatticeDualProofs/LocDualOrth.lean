import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEqKerAddRange

universe u

open Formalism.NG (KO annih)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

theorem mem_annih' {O A H : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup H] [Module O H]
    (pr : A →ₗ[O] H →ₗ[O] KO O) (M : Submodule O H) (x : A) :
    x ∈ annih pr M ↔ ∀ m ∈ M, pr x m = 0 := by
  simp only [annih, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]

theorem locTorsDual : StatLocTorsDual.{u} := by
  intro O A H _ _ _ _ _ _ _ pr M S a hS
  have hIm : (mulSub a M).map M.subtype ≤ M := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have h0 := Formalism.NG.annColength O A H pr M ((mulSub a M).map M.subtype) hIm
  rw [Submodule.comap_map_eq_of_injective M.injective_subtype] at h0
  refine le_trans ?_ h0
  have hSle : S ≤ annih pr ((mulSub a M).map M.subtype) := by
    intro s hs
    rw [mem_annih']
    rintro _ ⟨x, ⟨m, rfl⟩, rfl⟩
    have := (mem_annih' pr M _).1 (hS s hs) m m.2
    simpa only [LinearMap.lsmul_apply, Submodule.subtype_apply, Submodule.coe_smul, map_smul,
      LinearMap.smul_apply] using this
  let f : (S ⧸ (annih pr M).comap S.subtype) →ₗ[O]
      (annih pr ((mulSub a M).map M.subtype) ⧸
        (annih pr M).comap (annih pr ((mulSub a M).map M.subtype)).subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hSle) (by
      intro x hx
      exact hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    intro hx
    have hx' : (Submodule.Quotient.mk (Submodule.inclusion hSle x) :
        (annih pr ((mulSub a M).map M.subtype) ⧸
          (annih pr M).comap (annih pr ((mulSub a M).map M.subtype)).subtype)) = 0 := hx
    have hx'' := (Submodule.Quotient.mk_eq_zero _).1 hx'
    exact (Submodule.Quotient.mk_eq_zero _).2 hx''

end Formalism.RepresentationBoundsCohomology.LOC
