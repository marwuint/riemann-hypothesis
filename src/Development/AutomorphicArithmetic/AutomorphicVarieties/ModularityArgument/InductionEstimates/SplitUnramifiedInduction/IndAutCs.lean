import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IndGlue

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Base UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem infOf_two (m : Fin 2 → ℤ) : infOf m = {1 / 2 + (m 0 : ℂ), 1 / 2 + (m 1 : ℂ)} := by
  have e : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
  rw [infOf, e]
  rfl

private theorem infOf_add {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) :
    (infOf m + infOf m').Nodup ∧ ∀ z ∈ infOf m + infOf m', ∃ n : ℤ, z = (n : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 := by
  have e : infOf m + infOf m' = Finset.univ.val.map fun i => 1 / 2 + ((![m 0, m 1, m' 0, m' 1] i : ℤ) : ℂ) := by
    rw [infOf_two, infOf_two]
    rfl
  rw [e]
  refine ⟨Finset.univ.nodup.map fun i j hij => h (Int.cast_injective (add_left_cancel hij)), fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨![m 0, m 1, m' 0, m' 1] i - 1, by push_cast; ring⟩

private theorem tw_back {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    (R : G F Ω →* GL (Fin 4) (Qbar l)) : R = tw (tw R (cycBar F Ω l)⁻¹) (cycBar F Ω l ^ (1 : ℤ) * 1) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, ← Units.val_mul]
  simp

