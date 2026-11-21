import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients

noncomputable section

namespace GlobalTheory.ParAtCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

theorem isHalf_of_level (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.IsHalf D l.Mb :=
  ⟨l.fromK, hl.1 ▸ l.prod, l.coprime⟩

theorem levelAt_spec (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : HalfLevelCoefficients.IsHalf D Mb) :
    (HalfLevelCoefficients.levelAt D Mb h).M = D.host.g 0 * D.host.g 1 ∧ (HalfLevelCoefficients.levelAt D Mb h).A = 1 :=
  ⟨rfl, rfl⟩

theorem datAt_eq (D : D7) : HalfLevelCoefficients.datAt D = datumAtLift D _ (datHolds D) := rfl

theorem parAt_levelAt (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : Ideal (𝓞 D.host.E))
    (h : HalfLevelCoefficients.IsHalf D Mb) :
    Formalism.L2.Pj.parAt D hF hz hN (HalfLevelCoefficients.levelAt D Mb h) (levelAt_spec D Mb h) = HalfLevelCoefficients.parAt D hF hz hN Mb h :=
  rfl

theorem levelPb_iff (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) :
    LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb) := by
  constructor
  · rintro ⟨l, hl, hb⟩
    have h := isHalf_of_level D l hl
    rw [hb] at h
    exact h
  · intro h
    exact ⟨HalfLevelCoefficients.levelAt D _ h, levelAt_spec D _ h, rfl⟩

end GlobalTheory.ParAtCompare
