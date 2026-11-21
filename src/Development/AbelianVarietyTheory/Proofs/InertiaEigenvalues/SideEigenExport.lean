import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharactersEqLadicCharactersAllReadings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTripleEigenvectorInGoodPart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallRingElemOfFractionMapIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

theorem isInv_twGL_iff {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (W : Submodule K (Fin a → K)) : IsInv (twGL χ r) W ↔ IsInv r W := by
  constructor
  · intro h g v hv
    have := W.smul_mem (((χ g)⁻¹ : Kˣ) : K) (h g v hv)
    rwa [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at this
  · intro h g v hv
    rw [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (h : IsSSRep r) : IsSSRep (twGL χ r) := fun W hW =>
  let ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff χ r W).1 hW)
  ⟨W', (isInv_twGL_iff χ r W').2 h1, h2⟩

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

end GlobalTheory.TripInhab

namespace GlobalTheory.TripInhab

end GlobalTheory.TripInhab

end
