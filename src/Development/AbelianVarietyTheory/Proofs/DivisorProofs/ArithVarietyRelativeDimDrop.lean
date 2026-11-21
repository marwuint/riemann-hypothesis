import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory

theorem dim_ne_zero_of_isProjOver {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k)
    [IsIntegral Z] (hq : IsProjOver q) (hfin : Module.Finite ℤ k) (hc : CharZero Γ(Z, ⊤)) :
    topologicalKrullDim Z ≠ 0 := fun h0 => by
  obtain ⟨N, j, _, hj⟩ := hq
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hfin)
  let t := q ≫ spMap (Int.castRingHom k)
  have : Flat t := (flat_int_iff_charZero t).2 hc
  obtain ⟨z, -, hz⟩ := Flat.generalizingMap t (genericPoint_specializes (t (genericPoint Z)))
  have hs : Set.range t = Set.univ := by
    rw [← t.isClosedMap.isClosed_range.closure_eq]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec (Sp ℤ)).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ⟨z, hz⟩)))
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (TopologicalSpace.IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hs' := Set.range_eq_univ.1 hs
  obtain ⟨a, ha⟩ := hs' (⊥ : PrimeSpectrum ℤ)
  obtain ⟨b, hb⟩ := hs' (⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2
    Int.prime_two⟩ : PrimeSpectrum ℤ)
  have e := congrArg PrimeSpectrum.asIdeal (hb.symm.trans (((hu b).trans (hu a).symm) ▸ ha))
  exact two_ne_zero (Ideal.span_singleton_eq_bot.1 e)

end GlobalTheory
