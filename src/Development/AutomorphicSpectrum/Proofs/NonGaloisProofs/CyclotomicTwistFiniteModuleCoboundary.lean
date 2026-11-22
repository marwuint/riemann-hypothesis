import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCocycle

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

theorem GlobalTheory.CompanionTheory.LocDual.cup_flip_cob {G W W' R : Type} [Group G] [TopologicalSpace G] [AddCommGroup W]
    [AddCommGroup W'] [CommRing R] (χ : G → R) (a : G → W →+ W) (a' : G → W' →+ W') (P : W →+ W' →+ R)
    (hP : ∀ g x y, P (a g x) (a' g y) = χ g * P x y) (y : G → W) (x : G → W')
    (hy : IsLocallyConstant y ∧ ∀ g h, y (g * h) = y g + a g (y h))
    (hx : IsLocallyConstant x ∧ ∀ g h, x (g * h) = x g + a' g (x h)) (z z' : G × G → R)
    (hz : (z = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z' = (fun p => P (a p.1 (y p.2)) (x p.1))) ∨
      (z' = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z = (fun p => P (a p.1 (y p.2)) (x p.1))))
    (h : ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z (g, h)) :
    ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z' (g, h) := by
  obtain ⟨f, hf, hfd⟩ := h
  have hlc : IsLocallyConstant fun g => P (y g) (x g) :=
    IsLocallyConstant.comp₂ hy.1 hx.1 fun u v => P u v
  have hid : ∀ g h, χ g * P (y h) (x h) - P (y (g * h)) (x (g * h)) + P (y g) (x g) =
      -P (y g) (a' g (x h)) - P (a g (y h)) (x g) := by
    intro g h
    rw [hy.2, hx.2, ← hP]
    simp only [map_add, AddMonoidHom.add_apply]
    abel
  refine ⟨fun g => -P (y g) (x g) - f g, (hlc.neg).sub hf, fun g h => ?_⟩
  have h1 := hid g h
  have h2 := hfd g h
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only at h2 ⊢ <;> linear_combination -h1 - h2

