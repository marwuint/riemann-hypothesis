import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtChar

open GlobalTheory.HTMap

section Gen

theorem prim_map {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [CharZero O] (x : A →+* O) {q : ℕ}
    (hq : q ≠ 0) {ζ : A} (hζ : IsPrimitiveRoot ζ q) : IsPrimitiveRoot (x ζ) q := by
  haveI : NeZero (q : O) := ⟨Nat.cast_ne_zero.2 hq⟩
  have h := hζ.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)
  rw [← Polynomial.isRoot_cyclotomic_iff, Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic q x, Polynomial.eval_map,
    Polynomial.eval₂_hom, h.eq_zero, map_zero]

theorem root_mem {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {q : ℕ} (hq : q ≠ 0) {u : K} (hu : u ^ q = 1) : ∃ a : R, algebraMap R K a = u :=
  IsIntegrallyClosed.isIntegral_iff.1 ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hq, by simp [hu]⟩

def torsEquiv {M N : Type} [CommGroup M] [CommGroup N] (Φ : M ≃* N) (q : ℕ) :
    (powMonoidHom q : M →* M).ker ≃* (powMonoidHom q : N →* N).ker where
  toFun a := ⟨Φ a, MonoidHom.mem_ker.2 (by rw [powMonoidHom_apply, ← map_pow, ← powMonoidHom_apply, MonoidHom.mem_ker.1 a.2, map_one])⟩
  invFun b := ⟨Φ.symm b, MonoidHom.mem_ker.2 (by rw [powMonoidHom_apply, ← map_pow, ← powMonoidHom_apply, MonoidHom.mem_ker.1 b.2, map_one])⟩
  left_inv a := Subtype.ext (Φ.symm_apply_apply a.1)
  right_inv b := Subtype.ext (Φ.apply_symm_apply b.1)
  map_mul' a a' := Subtype.ext (map_mul Φ a.1 a'.1)

end Gen

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {T T' : Scheme.{0}} {y : T ⟶ X} {y' : T' ⟶ X}

def pullEquiv (g : T' ⟶ T) (g' : T ⟶ T') (h : g ≫ y = y') (h' : g' ≫ y' = y) (e₁ : g' ≫ g = 𝟙 T) (e₂ : g ≫ g' = 𝟙 T') :
    (Over.mk y ⟶ G) ≃* (Over.mk y' ⟶ G) where
  toFun := pull g h
  invFun := pull g' h'
  left_inv w := Over.OverMorphism.ext (by rw [pull_left, pull_left, ← Category.assoc, e₁, Category.id_comp])
  right_inv w := Over.OverMorphism.ext (by rw [pull_left, pull_left, ← Category.assoc, e₂, Category.id_comp])
  map_mul' := map_mul (pull g h)

end Pull

section Frac

variable (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def fracToK : FractionRing R →+* K := (FractionRing.algEquiv R K).toRingEquiv.toRingHom

def kToFrac : K →+* FractionRing R := (FractionRing.algEquiv R K).symm.toRingEquiv.toRingHom

theorem fracToK_comp : (fracToK R K).comp (algebraMap R (FractionRing R)) = algebraMap R K :=
  RingHom.ext fun a => (FractionRing.algEquiv R K).commutes a

theorem kToFrac_comp : (kToFrac R K).comp (algebraMap R K) = algebraMap R (FractionRing R) :=
  RingHom.ext fun a => (FractionRing.algEquiv R K).symm.commutes a

theorem fracToK_kToFrac : (fracToK R K).comp (kToFrac R K) = RingHom.id K :=
  RingHom.ext fun a => (FractionRing.algEquiv R K).apply_symm_apply a

theorem kToFrac_fracToK : (kToFrac R K).comp (fracToK R K) = RingHom.id _ :=
  RingHom.ext fun a => (FractionRing.algEquiv R K).symm_apply_apply a

end Frac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Tr

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (x : Sp R ⟶ X) (q : ℕ)

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

def trEquiv : Gam t x q ≃* TorsK t (spMap (algebraMap R K) ≫ x) q :=
  torsEquiv (pullEquiv (G := t.G) (spMap (fracToK R K)) (spMap (kToFrac R K))
    (by rw [spc_assoc, fracToK_comp]) (by rw [spc_assoc, kToFrac_comp])
    (by rw [spc, kToFrac_fracToK, spMap_id']) (by rw [spc, fracToK_kToFrac, spMap_id'])) q

def gen {x : Sp R ⟶ X} {q : ℕ} (σ : Over.mk x ⟶ t.G) (hσ : σ ^ q = 1) : Gam t x q :=
  ⟨pull _ rfl σ, MonoidHom.mem_ker.2 (by rw [powMonoidHom_apply, ← map_pow, hσ, map_one])⟩

end Tr

section Pts

variable {A : Type} [CommRing A] [IsDomain A] {x₀ : Sp A ⟶ X} {q : ℕ}

theorem at_pt {P : FP t x₀ q} {𝔮 : Ideal A} (hP : P.Full 𝔮) (h𝔮 : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪 = 𝔮)
    {χ₀ : Gam t x₀ q →* Aˣ} {b : P.Bˣ} (hb : P.Gl (kap χ₀) b) (σ : Over.mk x₀ ⟶ t.G) (hσ : σ ^ q = 1) :
    ∃ β₀ : P.B →+* A, P.At (RingHom.id A) σ.left β₀ ∧ β₀ b = χ₀ (gen σ hσ) := by
  obtain ⟨β₀, hβ₀⟩ := hP.at (φ := RingHom.id A) (fun 𝔪 h𝔪 => by rw [Ideal.comap_id]; exact h𝔮 𝔪 h𝔪) (y := x₀)
    (by rw [spMap_id', Category.id_comp]) σ hσ
  refine ⟨β₀, hβ₀, ?_⟩
  have h2 := hβ₀.map (algebraMap A (FractionRing A))
  rw [RingHom.comp_id] at h2
  have h3 := hb.1 (gen σ hσ).1.left _ h2
  rw [kap_left] at h3
  exact IsFractionRing.injective A (FractionRing A) h3

end Pts

section Chi

variable {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {q : ℕ}

end Chi

theorem ker_pow {M : Type} [CommGroup M] {q : ℕ} (a : (powMonoidHom q : M →* M).ker) : a ^ q = 1 :=
  Subtype.ext (MonoidHom.mem_ker.1 a.2)

end GlobalTheory.HtChar
