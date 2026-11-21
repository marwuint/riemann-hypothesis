import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.SelBaseChange

section Coh

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M'] [Module R M'] [IsScalarTower R R' M']
  (ρ : Representation R G M) (ρ' : Representation R' G M') (u : M' →ₗ[R] M) (hu : Continuous u)
  (he : ∀ g m, u (ρ' g m) = ρ g (u m))

def cZ : Z1 ρ' →ₗ[R] Z1 ρ where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add, he]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

def cH : H1 ρ' →ₗ[R] H1 ρ :=
  Submodule.mapQ (((B1 ρ').comap (Z1 ρ').subtype).restrictScalars R) _ (cZ ρ ρ' u hu he)
    (fun f hf => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hf
      refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
      have e := hm g
      simp only [Submodule.coe_subtype] at e
      change u (f.1 g) = _
      rw [e, map_sub, he]) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R ((B1 ρ').comap (Z1 ρ').subtype)).symm.toLinearMap

theorem cH_mk (z : Z1 ρ') :
    cH ρ ρ' u hu he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (cZ ρ ρ' u hu he z) := rfl

theorem res_cH {H : Type} [Group H] [TopologicalSpace H] (φ : H →* G) (hφ : Continuous φ)
    (x : H1 ρ') :
    resH1 ρ φ hφ (cH ρ ρ' u hu he x) =
      cH (ρ.comp φ) (ρ'.comp φ) u hu (fun _ _ => he _ _) (resH1 ρ' φ hφ x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem cH_mem_H1ur (J : Subgroup G) (x : H1 ρ') (hx : x ∈ H1ur ρ' J) :
    cH ρ ρ' u hu he x ∈ H1ur ρ J := by
  unfold H1ur at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  exact (res_cH ρ ρ' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ hx).trans (map_zero _))

theorem cH_mem_Sel {I : Type} {Dc : I → Type} [∀ v, Group (Dc v)] [∀ v, TopologicalSpace (Dc v)]
    (φ : ∀ v, Dc v →* G) (hφ : ∀ v, Continuous (φ v)) (L : LocCond ρ φ) (L' : LocCond ρ' φ)
    (h : ∀ v, ∀ x ∈ L' v, cH (ρ.comp (φ v)) (ρ'.comp (φ v)) u hu (fun _ _ => he _ _) x ∈ L v)
    (x : H1 ρ') (hx : x ∈ Sel ρ' φ hφ L') : cH ρ ρ' u hu he x ∈ Sel ρ φ hφ L := by
  rw [mem_Sel] at hx ⊢
  intro v
  rw [res_cH]
  exact h v _ (hx v)

theorem eq_zero_of_cH {ι : Type} (u : ι → (M' →ₗ[R] M)) (hu : ∀ i, Continuous (u i))
    (he : ∀ i g m, u i (ρ' g m) = ρ g (u i m))
    (hb : Function.Bijective fun (m : M') (i : ι) => u i m) (x : H1 ρ')
    (hx : ∀ i, cH ρ ρ' (u i) (hu i) (he i) x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [cH_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at hx ⊢
  choose m hm using hx
  obtain ⟨m', hm'⟩ := hb.2 m
  refine ⟨m', fun g => hb.1 (funext fun i => ?_)⟩
  have := hm i g
  rw [← congrFun hm' i] at this
  show u i _ = u i _
  rw [map_sub, he]
  exact this

end Coh

end GlobalTheory.SelBaseChange
