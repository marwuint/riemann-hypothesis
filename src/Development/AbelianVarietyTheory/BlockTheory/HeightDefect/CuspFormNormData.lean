import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ThetaWeightHeightConstants
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TotallyPositiveExponents

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree

open Formalism.BasicNotions NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents
open scoped TensorProduct ComplexOrder

def Kfld (D : D7) : IntermediateField ℚ D.what₂.LL :=
  IntermediateField.adjoin ℚ (Set.range D.what₂.OtoLL)

def KK (D : D7) : Type := ↥(Kfld D)

instance (D : D7) : Field (KK D) := inferInstanceAs (Field ↥(Kfld D))
instance (D : D7) : NumberField (KK D) := inferInstanceAs (NumberField ↥(Kfld D))

def incl (D : D7) : KK D →+* D.what₂.LL := (Kfld D).val.toRingHom

abbrev OO (D : D7) : Type := 𝓞 (KK D)

abbrev Place (D : D7) : Type := HeightOneSpectrum (OO D)

abbrev Emb (D : D7) : Type := KK D →+* ℂ

def emb0 (D : D7) : Emb D := D.what₂.embLL.comp (incl D)

instance (D : D7) : Algebra (KK D) ℂ := (emb0 D).toAlgebra

def logN {D : D7} (l : Place D) : ℝ := Real.log (Ideal.absNorm l.asIdeal : ℝ)

open Classical in

def vK {D : D7} (l : Place D) (a : KK D) : WithTop ℝ :=
  if a = 0 then ⊤ else (((vAdd l a : ℤ) : ℝ) : WithTop ℝ)

abbrev Wsp (D : D7) (j : Lift D.R) : @HSpace D.host.E _ _ D.host.cmStar :=
  letI := D.host.cmStar; D.sp.W j.1

abbrev WV (D : D7) (j : Lift D.R) : Type := letI := D.host.cmStar; (Wsp D j).V

def hW (D : D7) (j : Lift D.R) (x y : WV D j) : D.host.E := letI := D.host.cmStar; (Wsp D j).hD x y

structure CuspGeom (D : D7) (j : Lift D.R) where
  lat : letI := D.host.cmStar; Submodule (𝓞 D.host.E) (WV D j)
  lat_lat : letI := D.host.cmStar; Submodule.IsLattice D.host.E lat
  lat_unimod : letI := D.host.cmStar; Formalism.HermitianLatticesTheory.IsUnimodular (Wsp D j).hT lat
  frame : letI := D.host.cmStar; V D.host (rho j) →ₗ[D.host.E] WV D j
  frame_inj : Function.Injective frame
  frame_iso : ∀ u u', hW D j (frame u) (frame u') = 0

namespace CuspGeom

variable {D : D7} {j : Lift D.R} (c : CuspGeom D j)

def N : Submodule (𝓞 D.host.E) (V D.host (rho j)) :=
  letI := D.host.cmStar; c.lat.comap (c.frame.restrictScalars (𝓞 D.host.E))

def X : Submodule (𝓞 D.host.E) (V D.host (rho j)) := charLattice c.N

def Conj (c c' : CuspGeom D j) : Prop :=
  letI := D.host.cmStar
  ∃ γ : WV D j ≃ₗ[D.host.E] WV D j, (∀ x y, hW D j (γ x) (γ y) = hW D j x y) ∧
    (∀ x, γ x ∈ c'.lat ↔ x ∈ c.lat) ∧
    ∀ x, γ x ∈ LinearMap.range c'.frame ↔ x ∈ LinearMap.range c.frame

theorem Conj.refl : c.Conj c := by
  letI := D.host.cmStar
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

end CuspGeom

def zeroWt (D : D7) (j : Lift D.R) : ThetaWeight D j where
  plus := 0
  minus := 0
  plus_anti _ := antitone_const
  minus_anti _ := antitone_const
  n := 0

structure FormsRecord (D : D7) where

  Cusp : (j : Lift D.R) → ThetaWeight D j → Type
  [acg : ∀ j G, AddCommGroup (Cusp j G)]
  [modK : ∀ j G, Module (KK D) (Cusp j G)]
  [fd : ∀ j G, FiniteDimensional (KK D) (Cusp j G)]

  mul : ∀ {j} {G G' : ThetaWeight D j}, Cusp j G →ₗ[KK D] Cusp j G' →ₗ[KK D] Cusp j (G.add G')
  mul_comm : ∀ {j} {G G' : ThetaWeight D j} (f : Cusp j G) (g : Cusp j G'), HEq (mul f g) (mul g f)
  mul_assoc : ∀ {j} {G G' G'' : ThetaWeight D j} (f : Cusp j G) (g : Cusp j G') (h : Cusp j G''),
    HEq (mul (mul f g) h) (mul f (mul g h))

  one : ∀ j, rho j = 0 → Cusp j (zeroWt D j)
  one_mul : ∀ j (h : rho j = 0) (G : ThetaWeight D j) (f : Cusp j G), HEq (mul (one j h) f) f

  Pt : Lift D.R → Type
  place : ∀ {j}, Pt j → Place D

  vAt : ∀ {j} {G : ThetaWeight D j}, Pt j → Cusp j G → WithTop ℝ
  vAt_smul : ∀ {j} {G : ThetaWeight D j} (y : Pt j) (a : KK D) (f : Cusp j G),
    vAt y (a • f) = vK (place y) a + vAt y f
  vAt_add : ∀ {j} {G : ThetaWeight D j} (y : Pt j) (f g : Cusp j G),
    min (vAt y f) (vAt y g) ≤ vAt y (f + g)
  vAt_mul : ∀ {j} {G G' : ThetaWeight D j} (y : Pt j) (f : Cusp j G) (g : Cusp j G'),
    vAt y (mul f g) = vAt y f + vAt y g

  vAt_discrete : ∀ {j} (y : Pt j), ∃ e : ℕ, 0 < e ∧ ∀ (G : ThetaWeight D j) (f : Cusp j G) (t : ℝ),
    vAt y f = (t : WithTop ℝ) → ∃ z : ℤ, e * t = z

  sup : ∀ {j} {G : ThetaWeight D j}, Emb D → Cusp j G → ℝ
  sup_smul : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (a : KK D) (f : Cusp j G),
    sup σ (a • f) = ‖σ a‖ * sup σ f
  sup_add : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f g : Cusp j G), sup σ (f + g) ≤ sup σ f + sup σ g
  sup_mul : ∀ {j} {G G' : ThetaWeight D j} (σ : Emb D) (f : Cusp j G) (g : Cusp j G'),
    sup σ (mul f g) ≤ sup σ f * sup σ g
  sup_mul_self : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f : Cusp j G), sup σ (mul f f) = sup σ f ^ 2
  sup_conj : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f : Cusp j G),
    sup (ComplexEmbedding.conjugate σ) f = sup σ f

  ip : ∀ {j} {G : ThetaWeight D j}, Emb D → Cusp j G → Cusp j G → ℂ
  ip_add : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f f' g : Cusp j G),
    ip σ (f + f') g = ip σ f g + ip σ f' g
  ip_smul : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (a : KK D) (f g : Cusp j G),
    ip σ (a • f) g = σ a * ip σ f g
  ip_symm : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f g : Cusp j G),
    ip σ g f = starRingEnd ℂ (ip σ f g)

  ip_posDef : ∀ {j} {G : ThetaWeight D j} (σ : Emb D), ∃ (n : ℕ) (b : Module.Basis (Fin n) (KK D) (Cusp j G)),
    (Matrix.of fun i k => ip σ (b i) (b k)).PosDef
  ip_conj : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f g : Cusp j G),
    ip (ComplexEmbedding.conjugate σ) f g = starRingEnd ℂ (ip σ f g)

  l2_norm_le_sup_norm : ∀ {j} {G : ThetaWeight D j} (σ : Emb D) (f : Cusp j G), √(ip σ f f).re ≤ sup σ f
  l2_norm_mul : ∀ {j} {G G' : ThetaWeight D j} (σ : Emb D) (f : Cusp j G) (g : Cusp j G'),
    √(ip σ (mul f g) (mul f g)).re ≤ sup σ f * √(ip σ g g).re

  MaxCusp : Lift D.R → Type
  geom : ∀ {j}, MaxCusp j → CuspGeom D j
  geom_cover : ∀ j, 0 < rho j → ∀ c : CuspGeom D j, ∃ a : MaxCusp j, c.Conj (geom a)
  no_cusp : ∀ j, rho j = 0 → IsEmpty (MaxCusp j)

  Coef : ∀ {j} (a : MaxCusp j), ThetaWeight D j → expGroup (geom a).X → Type
  [coefAcg : ∀ {j} (a : MaxCusp j) G χ, AddCommGroup (Coef a G χ)]
  [coefMod : ∀ {j} (a : MaxCusp j) G χ, Module ℂ (Coef a G χ)]

  fj : ∀ {j} (a : MaxCusp j) (G : ThetaWeight D j) (χ : expGroup (geom a).X),
    (ℂ ⊗[KK D] Cusp j G) →ₗ[ℂ] Coef a G χ

attribute [instance] FormsRecord.acg FormsRecord.modK FormsRecord.fd FormsRecord.coefAcg FormsRecord.coefMod

namespace FormsRecord

variable {D : D7} (Φ : FormsRecord D) {j : Lift D.R}

instance modO (G : ThetaWeight D j) : Module (OO D) (Φ.Cusp j G) :=
  Module.compHom _ (algebraMap (OO D) (KK D))

instance tower (G : ThetaWeight D j) : IsScalarTower (OO D) (KK D) (Φ.Cusp j G) :=
  ⟨fun a b f => by
    change (a • b) • f = (algebraMap (OO D) (KK D) a) • (b • f)
    rw [Algebra.smul_def, mul_smul]⟩

end FormsRecord

namespace FormsRecord

end FormsRecord

end GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree

end
