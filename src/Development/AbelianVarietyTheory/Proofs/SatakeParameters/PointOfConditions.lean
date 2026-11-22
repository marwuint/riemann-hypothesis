import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowPointLoc

theorem continuous_of_adic {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A ≃+* B) :
    Continuous f := by
  have hm : Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map (f.symm : B →+* A)
    simpa using this
  refine continuous_of_continuousAt_zero (f : A →+ B) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := ((isAdic_iff.1 hB).2 s hs)
  have hopen := (isAdic_iff.1 hA).1 n
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds (Ideal.zero_mem _)) ?_)
  intro x hx
  apply hn
  have h1 : f x ∈ Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

end GlobalTheory.RowPointLoc
