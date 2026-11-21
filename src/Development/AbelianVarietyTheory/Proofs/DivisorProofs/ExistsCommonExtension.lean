import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

open NumberField IsDedekindDomain TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt GlobalTheory.FlagTan

theorem finite_of_finRes {T₀ T : CDVR} (hT : T.FinRes) (g : T₀.V →+* T.V) (hg : Function.Injective g)
    [IsLocalHom g] : g.Finite := by
  letI := g.toAlgebra
  haveI : Finite (T.V ⧸ maximalIdeal T.V) := hT
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  refine GlobalTheory.finite_of_forall_prime_mem (R := T₀.V) (B := T.V) hp.ne_zero (fun P hP h0 => ?_) ?_ ?_
  · rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hp.not_isUnit
  · exact fun h => IsDiscreteValuationRing.not_a_field _ ((Ideal.map_eq_bot_iff_of_injective hg).1 h)
  · exact ne_top_of_le_ne_top (maximalIdeal.isMaximal T.V).ne_top (map_maximalIdeal_le g)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [NumberField K] [Algebra c.F K] {y : FrPt Xo c K}
  {v : FinitePlace K}

end GlobalTheory.CompHS
