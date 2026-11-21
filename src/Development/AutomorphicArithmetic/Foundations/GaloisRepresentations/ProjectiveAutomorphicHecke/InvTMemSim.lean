import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

theorem invT_val {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : (invT n R g).val = (g⁻¹).valᵀ := rfl

@[simp] theorem invT_invT' {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  rw [invT_val, ← map_inv, invT_val, inv_inv, transpose_transpose]

theorem invT_mem_Sim {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {i : B →+* A} {n : ℕ} {p : GL (Fin n) A × Bˣ}
    (h : p ∈ Sim σ i n) : (invT n A p.1, p.2⁻¹) ∈ Sim σ i n := by
  have h1 := mem_Sim.1 h
  have h2 : p.1.valᵀ * p.1.val.map σ = i p.2 • (1 : Matrix (Fin n) (Fin n) A) := by
    have := congrArg transpose h1
    rwa [transpose_mul, transpose_transpose, transpose_smul, transpose_one] at this
  have h3 : i (p.2⁻¹ : Bˣ) * i p.2 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h4 : (p.1⁻¹).valᵀ * p.1.valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have h5 : (p.1⁻¹).val.map σ * p.1.val.map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h6 : p.1.val.map σ = i p.2 • (p.1⁻¹).valᵀ := by
    rw [← Matrix.one_mul (p.1.val.map σ), ← h4, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one]
  refine mem_Sim.2 ?_
  show (((p.1⁻¹).valᵀ).map σ)ᵀ * (p.1⁻¹).valᵀ = i (p.2⁻¹ : Bˣ) • 1
  rw [transpose_map, transpose_transpose, ← h5, h6, Matrix.mul_smul, smul_smul, h3, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def th : GUf E n →* GUf E n :=
  (((invT n (Af E)).prodMap invMonoidHom).comp (GUf E n).subtype).codRestrict _ fun g => invT_mem_Sim g.2

def th0 : Gam0 E n →* Gam0 E n :=
  (((invT n E).prodMap invMonoidHom).comp (Gam0 E n).subtype).codRestrict _ fun g =>
    ⟨invT_mem_Sim g.2.1, (Units.posSubgroup ℚ).inv_mem g.2.2⟩

@[simp] theorem sim_th (g : GUf E n) : sim (th g) = (sim g)⁻¹ := rfl

@[simp] theorem mat_th (g : GUf E n) : mat (th g) = invT n _ (mat g) := rfl

@[simp] theorem comp_th (w : Plc E) (g : GUf E n) : comp w (th g) = invT n _ (comp w g) := GlobalTheory.SplitPts.invT_map _ _

@[simp] theorem th_th (g : GUf E n) : th (th g) = g := Subtype.ext (Prod.ext (invT_invT' _) (inv_inv _))

theorem th_rat (γ : Gam0 E n) : th (rat γ) = rat (th0 γ) :=
  Subtype.ext (Prod.ext (GlobalTheory.SplitPts.invT_map _ _).symm (map_inv (Units.map (algebraMap ℚ AfQ).toMonoidHom) _).symm)

theorem guf_ext {g g' : GUf E n} (h1 : sim g = sim g') (h2 : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun w => congrArg Units.val (h2 w))) h1)

theorem invT_mem_KGL {w : Plc E} {y : GLw n w} (h : y ∈ KGL w n) : invT n _ y ∈ KGL w n := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨invT n _ z, GlobalTheory.SplitPts.invT_map _ z⟩

def levT (Kw : ∀ w : Plc E, Subgroup (GLw n w)) : ∀ w : Plc E, Subgroup (GLw n w) := fun w => (Kw w).comap (invT n _)

theorem th_mem_lev {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {k : GUf E n} :
    th k ∈ lev S Kw ↔ k ∈ lev S (levT Kw) := by
  simp only [mem_lev, sim_th, comp_th, inv_mem_iff, levT, Subgroup.mem_comap]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₃_congr fun w _ _ => ⟨fun h => ?_, invT_mem_KGL⟩
  simpa using invT_mem_KGL h

def ThLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ (w : Plc E) (hw : IsSplitAt w) (y : GLw n w), th (loc hw y) = loc hw (invT n _ y)) ∧
    (0 < n → ∀ (x : E) (w : Plc E) (z : GUf E n), IsCen x w z → th z = z⁻¹)

end UpperTheory.Gal.CertificateRingHomMap

end
