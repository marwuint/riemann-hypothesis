import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec

noncomputable section
namespace GlobalTheory.RecDictModel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RecDict
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

variable {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty}

theorem th_conj {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (z : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    θ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ z) := by
  have hτ : ∀ x : D.host.E, τ (star x) = starRingEnd ℂ (τ x) := fun x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hre : ∀ a : Ainf D.host.F, starRingEnd ℂ (θ (a ⊗ₜ[D.host.F] (1 : D.host.E))) = θ (a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro a
    refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
      (isClosed_eq (Complex.continuous_conj.comp h.2) h.2) fun f => ?_
    have e : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
      exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f |>.trans
        ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
    erw [e, h.1, ← hτ]
    rw [(D.sp.cm.fixed _).2 ⟨f, rfl⟩]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul a x =>
    have e : ∀ y : D.host.E, a ⊗ₜ[D.host.F] y = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      intro y; simp
    have e2 : sigR (Ainf D.host.F) D.sp.cm.sig (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] (star x) := rfl
    rw [e2, e (star x), e x, map_mul, map_mul, map_mul, hre, h.1, h.1, hτ]

theorem cT_map {A : Type} [CommRing A] {n : Type} (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M : Matrix n n A) :
    (Formalism.UG.cT s M).map φ = (M.map φ).conjTranspose := by
  ext a b
  exact h _

theorem uni_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) (hM : Formalism.UG.cT s M * J * M = J)
    (J' M' : Matrix n n ℂ) (hJ : J.map φ = J') (hM' : M' = M.map φ) : M'.conjTranspose * J' * M' = J' := by
  subst hJ hM'
  rw [← cT_map s φ h, ← Matrix.map_mul, ← Matrix.map_mul, hM]

set_option maxHeartbeats 800000 in
theorem archM_unitary (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) :
    (archM V θ g).conjTranspose * V.gram.map τ * archM V θ g = V.gram.map τ := by
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).1 * JR (AF D.host.F) V.gram * (matHom V g).1 =
      JR (AF D.host.F) V.gram := g.2
  let π : AF D.host.F ⊗[D.host.F] D.host.E →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hπ : ∀ z, π (sigR (AF D.host.F) D.sp.cm.sig z) = sigR (Ainf D.host.F) D.sp.cm.sig (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul a x => rfl
  have hJ : (JR (AF D.host.F) V.gram).map (θ.comp π) = V.gram.map τ := by
    ext a b
    exact h.1 _
  exact uni_map (sigR (AF D.host.F) D.sp.cm.sig) (θ.comp π) (fun z => (congrArg θ (hπ z)).trans (th_conj h (π z))) _ _ hg
    _ _ hJ rfl

theorem gram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G x = (x.conjTranspose * (G.map τ).transpose * x).transpose := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

end GlobalTheory.RecDictModel
