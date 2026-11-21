import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LatticeEmbeddingHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

noncomputable section

namespace GlobalTheory.DictPinCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase CongrAt half IsLatEmb crd vec IsModelOf IsOrthoFrame IsArchAt
  IsRatUnitary ratTo LatMark IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver AdelicU AdPinU)
open scoped TensorProduct nonZeroDivisors Matrix

abbrev conjHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toRingEquiv.toRingHom

section First

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)

def gramOf : Matrix (Fin n) (Fin n) E := Matrix.of fun a b => hT (fr a) (fr b)

def latHat : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Fin𝔸 F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ fr.repr x i}

def archM (th' : Inf𝔸 F ⊗[F] E →+* ℂ) (h : G) : Matrix (Fin n) (Fin n) ℂ := (infHom h).1.map th'

def finVec (v : Fin n → E) : Fin n → Fin𝔸 F ⊗[F] E := fun i => (1 : Fin𝔸 F) ⊗ₜ v i

def gLat (g : G) : Set (Fin n → Fin𝔸 F ⊗[F] E) :=
  (finHom g).1.mulVec '' (latHat F fr L0 : Set (Fin n → Fin𝔸 F ⊗[F] E))

def LatIsom {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 E] (Fin n → E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ E (xi0 * hT (fr.equivFun.symm (ι x)) (fr.equivFun.symm (ι y)))

def IsOrthogonalFrame (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def halfVec (b : 𝓞 E) (z : Fin n → Fin𝔸 F ⊗[F] E) : Fin n → Fin𝔸 F ⊗[F] E :=
  fun i => ((1 : Fin𝔸 F) ⊗ₜ (b : E)) * z i

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

def flipForm (x y : W) : E := hT y x

def IsRatPoints : Prop :=
  (∀ γ ∈ GQ, ∃ γ₀, IsRatUnitary fr (flipForm hT) γ₀ ∧ finHom γ = ratTo F (Fin𝔸 F) γ₀ ∧ infHom γ = ratTo F (Inf𝔸 F) γ₀) ∧
    ∀ γ₀, IsRatUnitary fr (flipForm hT) γ₀ →
      ∃ γ ∈ GQ, finHom γ = ratTo F (Fin𝔸 F) γ₀ ∧ infHom γ = ratTo F (Inf𝔸 F) γ₀

end First

section Compare

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)

def coord : W ≃ₗ[𝓞 E] (Fin n → E) := fr.equivFun.restrictScalars (𝓞 E)

theorem finVec_coord (v : W) : finVec F (coord fr v) = toFin F fr v := rfl

theorem latHat_eq : latHat F fr L0 = GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := rfl

theorem orthogonal_frame_iff (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : IsOrthogonalFrame X x₀ ↔ IsOrthoFrame X x₀ :=
  Iff.rfl

abbrev ad (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] (a : E) : Fin𝔸 F ⊗[F] E := 1 ⊗ₜ a

omit [NumberField E] [IsCMField E] in
theorem halfVec_eq (b : 𝓞 E) (z : Fin n → Fin𝔸 F ⊗[F] E) : halfVec F b z = ad F (algebraMap (𝓞 E) E b) • z := rfl

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

end Compare

end GlobalTheory.DictPinCompare
