import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsEigenvalueGLOneEqCuspidalLabelGen

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.DepthZeroModel
open GlobalTheory.SerSys.TameGen

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

abbrev tauOne (θ : (ZMod g)ˣ →* ℂˣ) : FDRep ℂ (Gn g 1) :=
  FDRep.of (GlobalTheory.GLp.Model.chRep (θ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1))))

theorem tauOne_character (θ : (ZMod g)ˣ →* ℂˣ) (y : Gn g 1) :
    (tauOne θ).character y = θ (Matrix.GeneralLinearGroup.det y) := by
  change LinearMap.trace ℂ ℂ (((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • LinearMap.id) = _
  simp

theorem exists_label (L : LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ) (u : (ZMod g)ˣ)
    (hu : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1) :
    ∃ P, IsCuspOf L P (tauOne θ).character ∧ liftPoly L.teich P = X - C (θ u : ℂ) := by
  obtain ⟨T, h1, -, h3⟩ := GlobalTheory.Published.GreenModel.green_one L
  have hc : GlobalTheory.GLq.IsCusp (tauOne θ).character := by
    refine ⟨one_pos, ?_, fun a h1 h2 => by omega⟩
    have := GlobalTheory.Published.GreenModel.isIrr_hom
      ((Units.coeHom ℂ).comp (θ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1) (R := ZMod g))))
    convert this using 1
    funext y
    exact tauOne_character θ y
  obtain ⟨P, hP, e⟩ := h3 _ hc
  have hP' : IsCuspOf L P (tauOne θ).character := e ▸ (h1 P hP).1
  refine ⟨P, hP', ?_⟩
  have hb : -P.coeff 0 ≠ 0 := neg_ne_zero.2 hP.2.2.1
  have hr : ∀ b : ZMod g, Formalism.CyclotomicNorms.rootsBar (X - C b) = {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) b} := fun b => by
    simp [Formalism.CyclotomicNorms.rootsBar]
  have hrP : Formalism.CyclotomicNorms.rootsBar P = {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)} :=
    (congrArg Formalism.CyclotomicNorms.rootsBar (GlobalTheory.Published.GreenModel.lab_eq hP)).trans (hr _)
  have hcp : ((Matrix.GeneralLinearGroup.scalar (Fin 1) u : Gn g 1) : Mt g 1).charpoly = X - C (u : ZMod g) := by
    simp [Matrix.charpoly, Matrix.GeneralLinearGroup.scalar]
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  have h4 := hP'.2.2 (algebraMap _ _ (-P.coeff 0)) (by rw [hrP]; simp) (Matrix.GeneralLinearGroup.scalar (Fin 1) u) (by rw [hcp]; exact irreducible_X_sub_C _)
      (L.gen 1) (by rw [hcp, hr, hu]; simp)
  have h5 := GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos (GlobalTheory.Published.GreenModel.alg_pow hb) 1
  rw [tauOne_character, hd] at h4
  simp only [pow_one] at h5
  simp only [Nat.sub_self, pow_zero, one_mul, Finset.range_one, Finset.sum_singleton, pow_one, h5] at h4
  rw [h4, liftPoly, hrP]
  simp

end GlobalTheory.Published.DepthZeroModel
