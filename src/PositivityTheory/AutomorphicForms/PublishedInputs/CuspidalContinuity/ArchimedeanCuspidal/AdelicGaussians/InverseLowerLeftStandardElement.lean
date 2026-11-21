import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA.YVp

instance countable_matrix2_number_field : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))

instance countable_GL2_number_field : Countable (GL (Fin 2) ℚ) := Units.val_injective.countable

instance countable_principal : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
  Set.Countable.to_subtype ((Set.countable_range (algebraMap ℚ 𝔸[ℚ])).mono fun _ hx => hx)

instance nontrivial_adele : Nontrivial 𝔸[ℚ] := by
  refine nontrivial_of_ne (0 : 𝔸[ℚ]) 1 fun h => adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun x => ?_)
  have hx : x = 0 := by rw [← mul_one x, ← h, mul_zero]
  rw [hx, AddChar.map_zero_eq_one, AddChar.one_apply]

end Ad3.GA.YVp

namespace Ad3.GA

end Ad3.GA
