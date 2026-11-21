import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RestrictAutomorphism
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
open GlobalTheory.UnramifiedCrys GlobalTheory.Cyc
open scoped Topology

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      (∀ g, (M g).map (zlW p R) * W.map (WittVector.map (ρ g).toRingHom) = W) ∧
      ∀ i j n, ∃ m, 0 < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n :=
  _root_.UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg ρ hopen M hM hJ

end

theorem UpperTheory.exists_algebraic_vector_spanning_subspace :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ℤ_[l]), Continuous M → (∀ g ∈ IK K, M g = 1) → ∃ W : Matrix (Fin r) (Fin r) (Ainf l), IsUnit W.det ∧ (∀ g, (M g).map (zlW l (OCb l)) * W.map (AI.actW (g : GQ l)) = W) ∧ ∀ i j n, ∃ m, 0 < m ∧ (W i j).coeff n ^ l ^ m = (W i j).coeff n := by
  intro l _ P AI K r M hM hI
  have := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  exact exists_alg (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (GlobalTheory.UnramifiedCrys.eventually_actT_eq AI y m hm hy)) M hM
    (fun g hg => hI g (Subgroup.subset_closure fun x hx =>
      GlobalTheory.UnramifiedCrys.norm_sub_lt_one_of_fix AI g hg x hx))
