import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Topology

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open Classical in

def sigMult (D : Datum H) (τ : E →+* ℂ) : ℕ := if τ (H.rt : E) = H.rt0 then D.p else D.q

def IsTypeFn (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, Nat.card {i : Fin g // ty i = τ} = sigMult D τ

def tyAct {g : ℕ} (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ :=
  fun i => ty i (a : E) * z i

def actR (D : Datum H) (a : 𝓞 E) : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
  (DistribMulAction.toLinearMap ℤ D.La a).baseChange ℝ

def sigTrace (D : Datum H) (a : 𝓞 E) : ℂ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
    ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E)))

def domain (D : Datum H) : Set (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) :=
  {J | (∀ x, J (J x) = -x) ∧
    (∀ a : 𝓞 E, J ∘ₗ actR D a = actR D a ∘ₗ J) ∧
    (∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) ∧
    ∀ a : 𝓞 E, ((LinearMap.trace ℝ _ (actR D a) : ℝ) : ℂ) / 2 -
      Complex.I * ((LinearMap.trace ℝ _ (J ∘ₗ actR D a) : ℝ) : ℂ) / 2 = sigTrace D a}

def Presents (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))
    (J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) : Prop :=
  ∃ φ : (ℝ ⊗[ℤ] D.La) ≃ₗ[ℝ] (Fin g → ℂ),
    (∀ x : D.La, φ ((1 : ℝ) ⊗ₜ[ℤ] x) = P x) ∧ (∀ v, φ (J v) = Complex.I • φ v) ∧
      ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v)

theorem domain_nonempty (D : Datum H) : (domain D).Nonempty := by
  obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
  have key := fun a : 𝓞 E => h4 a (actR D a) (sigTrace D a) (fun x => rfl) rfl
  refine ⟨J, h1, fun a => (key a).1, h2, h3, fun a => ?_⟩
  rw [(key a).2.1, (key a).2.2]
  apply Complex.ext
  · simp
  · simp; ring

end Period

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

def HolOn (B : Set V) (y : V → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens), ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ U →
    (∀ᶠ b' in 𝓝[B] b, ⊤ ≤ y b' ⁻¹ᵁ U) ∧
      ∀ f : Γ(X, U), DifferentiableWithinAt ℂ (fun b' => valAt' (y b') U f) B b

end Hol

section Theta

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}} {G : Over S} [GrpObj G] {g : ℕ}

abbrev fibre (G : Over S) (y : Sp ℂ ⟶ S) : Scheme.{0} := pullback G.hom y

def fibrePt {y : Sp ℂ ⟶ S} (x : Over.mk y ⟶ G) : Sp ℂ ⟶ fibre G y :=
  pullback.lift x.left (𝟙 (Sp ℂ)) (by simpa using Over.w x)

def IsRigFrame (L : RigLB G) (B : Set V) (y : V → (Sp ℂ ⟶ S))
    (ex : ∀ b : V, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (fr : L.L.ι → V → (Fin g → ℂ) → ℂ) : Prop :=
  HolOn (B ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun p => ((ex p.1 p.2).left : Sp ℂ ⟶ G.left)) ∧
  (∀ b ∈ B, (ex b 0).left = y b ≫ eSec G) ∧
  (∀ i, DifferentiableOn ℂ (fun p : V × (Fin g → ℂ) => fr i p.1 p.2)
    {p | p.1 ∈ B ∧ ⊤ ≤ (ex p.1 p.2).left ⁻¹ᵁ L.L.U i}) ∧
  (∀ i, ∀ b ∈ B, ∀ z, ⊤ ≤ (ex b z).left ⁻¹ᵁ L.L.U i → fr i b z ≠ 0) ∧
  (∀ i j, ∀ b ∈ B, ∀ z, ⊤ ≤ (ex b z).left ⁻¹ᵁ (L.L.U i ⊓ L.L.U j) →
    fr i b z = valAt' (X := G.left) (ex b z).left (L.L.U i ⊓ L.L.U j) (L.L.g i j).val * fr j b z) ∧
  ∀ (j : (L.L.pull (eSec G)).ι), ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ (L.L.pull (eSec G)).U j →
    fr (j PUnit.unit) b 0 = valAt' (X := S) (y b) ((L.L.pull (eSec G)).U j) (L.rig.s j).val

def IsFibreFn (L : LB G.left) (y : Sp ℂ ⟶ S) (ex : (Fin g → ℂ) → (Over.mk y ⟶ G))
    (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (L.pull (pullback.fst G.hom y)).ι) (z : Fin g → ℂ),
    ⊤ ≤ fibrePt (ex z) ⁻¹ᵁ (L.pull (pullback.fst G.hom y)).U j →
      valAt' (fibrePt (ex z)) ((L.pull (pullback.fst G.hom y)).U j) (s.f j) = θ z * fr (j PUnit.unit) z

def IsThetaFrame (L : RigLB G) (B : Set V) (y : V → (Sp ℂ ⟶ S))
    (ex : ∀ b : V, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (θ : V → (Fin g → ℂ) → ℂ)
    (fr : L.L.ι → V → (Fin g → ℂ) → ℂ) : Prop :=
  IsRigFrame L B y ex fr ∧
    ∀ b ∈ B, ∃ s : (L.L.pull (pullback.fst G.hom (y b))).Sec, IsFibreFn L.L (y b) (ex b) (fun i => fr i b) s (θ b)

end Theta

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
