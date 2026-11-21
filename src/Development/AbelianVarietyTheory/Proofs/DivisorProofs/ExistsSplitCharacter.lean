import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetChar

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

section Alg

variable {R : Type} [CommRing R]

def cut (a : R) (ha : a * a = a) : Rˣ →* Rˣ where
  toFun u := ⟨a * u + (1 - a), a * (u⁻¹ : Rˣ) + (1 - a),
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv,
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv⟩
  map_one' := Units.ext (by simp)
  map_mul' u w := Units.ext (by
    show a * ((u : R) * w) + (1 - a) = (a * u + (1 - a)) * (a * w + (1 - a))
    linear_combination (-((u : R) * w) + u + w - 1) * ha)

theorem cut_val (a : R) (ha : a * a = a) (u : Rˣ) : (cut a ha u : R) = a * u + (1 - a) := rfl

theorem continuous_cut [TopologicalSpace R] [IsTopologicalRing R] (a : R) (ha : a * a = a) :
    Continuous (cut a ha) :=
  Units.continuous_iff.2 ⟨(continuous_const.mul Units.continuous_val).add continuous_const,
    (continuous_const.mul Units.continuous_coe_inv).add continuous_const⟩

theorem mul_det {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, a * (M - 1) i j = 0) :
    a * M.det = a := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R a)
  have hI : ∀ x, x ∈ I ↔ x * a = 0 := fun x => Iff.rfl
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 ((hI _).2 ((mul_comm _ _).trans (h i j)))
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, h1, map_one, det_one, map_one]
  have h3 := (hI _).1 (Ideal.Quotient.eq.1 h2)
  linear_combination h3

end Alg

theorem char_norm {D : D7} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n)
    (x y : (Formalism.L2.Theta.AE D)ˣ) (hy : (y : Formalism.L2.Theta.AE D) = x * cA D x) : χ y = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  have := D.host.isCMField_hostE
  have e : y = idF D (Units.map (Algebra.norm (AF D.host.F) : Formalism.L2.Theta.AE D →* AF D.host.F) x) :=
    Units.ext (hy.trans (GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F)
      (x : Formalism.L2.Theta.AE D)).symm)
  rw [e, h η hη, hη.2.2.1, one_pow]

end GlobalTheory.SplitDetChar

end
