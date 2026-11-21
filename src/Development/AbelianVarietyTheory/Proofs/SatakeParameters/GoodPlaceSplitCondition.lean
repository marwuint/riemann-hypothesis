import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ValInert

theorem conjSelf (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hI : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) : IsConjPl D.host w w := by
  intro x y hxy
  have hw : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal = w.asIdeal := hI
  let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)
  have hσ : ∀ z : 𝓞 D.host.E, ((σ z : 𝓞 D.host.E) : D.host.E) = D.host.conj (z : D.host.E) := fun z => rfl
  have key : w.asIdeal ≤ Ideal.comap σ w.asIdeal := by
    conv_lhs => rw [← hw]
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : σ (algebraMap _ _ s) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
      apply RingOfIntegers.ext
      rw [hσ]
      have hm : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) ∈ D.host.F := by
        show ((s : D.host.F) : D.host.E) ∈ D.host.F
        exact (s : D.host.F).2
      exact (GlobalTheory.DesignBC.mem_F_iff D _).1 hm
    rw [e, ← hw]
    exact Ideal.mem_map_of_mem _ hs
  have hy : y = σ x := RingOfIntegers.ext (hxy.trans (hσ x).symm)
  have hx : x = σ y := RingOfIntegers.ext (by rw [hσ, hxy, GlobalTheory.DesignBC.conj_conj])
  exact ⟨fun h => hy ▸ key h, fun h => hx ▸ key h⟩

theorem notSplit (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : IsConjPl D.host w w) : ¬ IsSplitPl D.host w := by
  rintro ⟨x, hx, hy⟩
  obtain ⟨y, hy'⟩ : ∃ y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) :=
    ⟨RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x, rfl⟩
  exact hy y hy' ((h x y hy').1 hx)

theorem xi_eq {D : D7} {nch : NChoice D} {C C' : CharFrame D} (h : C = C') (T : TupTied D C nch) (T' : TupTied D C' nch)
    (h' : HEq T T') : T.xi = T'.xi := by
  subst h
  cases h'
  rfl

end GlobalTheory.ValInert
