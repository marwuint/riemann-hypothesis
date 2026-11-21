import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models

namespace GlobalTheory.FiniteStable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem aut_bar (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

@[reducible] def twist (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {S : Scheme.{0}} (t : SAB H S) : SAB H S where
  G := t.G
  semi := t.semi
  act :=
    { act := fun a => t.act.act (σ a)
      hom := fun a => t.act.hom _
      one := by rw [map_one, t.act.one]
      mul := fun a b => by rw [map_mul, t.act.mul]
      add := fun a b => by rw [map_add, t.act.add] }
  PP := t.PP
  cub := t.cub
  sym := t.sym
  adj a := by
    have := t.adj (σ a)
    rwa [← aut_bar] at this
  prim := by
    have := t.prim
    rwa [← hσ] at this

end GlobalTheory.FiniteStable
