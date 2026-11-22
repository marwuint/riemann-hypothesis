import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Complex
open GroundTheory.Global
open scoped NumberField.AdeleRing

namespace Ad3.GM

abbrev emb : ℚˣ →* IdeleGroup ℚ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom

def per (f : IdeleGroup ℚ → ℂ) (x : IdeleGroup ℚ) : ℂ := ∑' a : ℚˣ, f (emb a * x)

def pt (y : ℝ) (z : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : IdeleGroup ℚ :=
  moduleSection Rat.infinitePlace (expPos y) * IdeleGroup.ofFinite z

def phi (f : IdeleGroup ℚ → ℂ) (c : HeckeCharacter ℚ) (y : ℝ) : ℂ :=
  ∫ z in (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    per f (pt y z) * (c.toIdele (IdeleGroup.ofFinite z) : ℂ) ∂finiteIdeleMeasure ℚ

end Ad3.GM
