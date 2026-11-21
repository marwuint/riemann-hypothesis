import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MulVecMemLatMap

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Defs

def LieN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Y : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  cT σ Y * J + J * Y = 0 ∧ IsStrict A ∧ Y * P = P * A ∧ ∀ x ∈ perpX σ J P, Y *ᵥ x ∈ spanX P

def Relevant (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∀ Y A A', LieN σ J P Y A → LieN σ J P' Y A' →
    (simpleSum A - simpleSum A') + σ (simpleSum A - simpleSum A') = 0

def Unip {n r : ℕ} (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ a : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUp a ∧ P' = P * a

def LiesAt {r : ℕ} (w : Formalism.MainNotions.S.Point E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ l u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsLo l ∧ IsUp u ∧ Z * eps E r = l * Formalism.MainNotions.S.ptMat w * u

def onePt (E : Type) [Field E] (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) := ⟨[(1, r + 1)], by simp, by simp⟩

open scoped Classical in

def ptOfMat {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Formalism.MainNotions.S.Point E (r + 1) :=
  if h : ∃ w, LiesAt w Z then h.choose else onePt E r

variable [NumberField E]

def IntFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IsFrame σ J T P ∧ PrimIn (frameLat P) Λ

def Cong {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  frameLat ((g : E)⁻¹ • (P' - P)) ≤ Λ

def admitted (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T' : E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IntFrame σ J T' Λ P' ∧ ∃ u ∈ UO E r, Cong g Λ (P * u) P'

def defLat {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Λ ⊓ (frameLat P ⊔ frameLat P').comap ((g : 𝓞 E) • LinearMap.id)

def satLat {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  latIn Λ (Submodule.span E (M : Set (Fin n → E)))

abbrev Defect {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Type :=
  satLat M Λ ⧸ M.submoduleOf (satLat M Λ)

def DefectAt (F : Type) [Field F] [Algebra F E] {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E))
    (p : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ x : Defect M Λ, ∀ a : 𝓞 F, a ∉ p.asIdeal → algebraMap (𝓞 F) (𝓞 E) a • x ≠ 0

def NO (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {s | InN σ J P s ∧ latMap s Λ = Λ}

def Move (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P A B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s ∈ NO σ J Λ P, ∃ u ∈ UO E r, B = s * A * u

def Transp (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin (r + 1)) E)
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s, InS σ J P s ∧ latMap s Λ = Λ' ∧ ∃ u ∈ UO E r, B = s * A * u

end Defs

section Field

variable {σ : E →+* E} {n r : ℕ} {J s Y : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v A Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem LieN.of_isom (hJ : IsUnit J.det) (hs : IsUn σ J s) (h : LieN σ J (s * P) Y A) :
    LieN σ J P (s⁻¹ * Y * s) A := by
  have hu := isUnit_det_of_isUn hJ hs
  have l := Matrix.nonsing_inv_mul s hu
  have e1 : J * s⁻¹ = cT σ s * J := by
    conv_lhs => rw [← hs, Matrix.mul_assoc, Matrix.mul_nonsing_inv s hu, Matrix.mul_one]
  have e2 : cT σ s⁻¹ * J = J * s := by
    conv_rhs => rw [← isUn_inv hJ hs, Matrix.mul_assoc, l, Matrix.mul_one]
  refine ⟨?_, h.2.1, ?_, fun x hx => ?_⟩
  · have := congrArg (fun W => cT σ s * W * s) h.1
    rw [cT_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, e2, ← Matrix.mul_assoc J, ← Matrix.mul_assoc J, e1]
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul] using this
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, h.2.2.1, Matrix.mul_assoc, ← Matrix.mul_assoc, l, Matrix.one_mul]
  · have := mulVec_mem_spanX (s := s⁻¹) (h.2.2.2 _ ((mulVec_mem_perpX hs P x).2 hx))
    rwa [← Matrix.mul_assoc, l, Matrix.one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this

theorem Relevant.isom (hJ : IsUnit J.det) (hs : IsUn σ J s) (h : Relevant σ J P P') :
    Relevant σ J (s * P) (s * P') := fun _ _ _ h1 h2 => h _ _ _ (h1.of_isom hJ hs) (h2.of_isom hJ hs)

end Field

section Lattice

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' A B C : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ Λ' Λ'' M : Submodule (𝓞 E) (Fin n → E)} {T T' : E}

theorem exists_UO (hP : Free P) (h : PrimIn (frameLat P) Λ) (h' : PrimIn (frameLat P) (latMap s Λ))
    (hs : InS σ J P s) : ∃ a ∈ UO E r, s * P = P * a := by
  obtain ⟨-, a, ha, e⟩ := inS_iff.1 hs
  refine ⟨a, mem_UO_of_le hP ha fun x hx => h'.2 x ?_ ?_, e⟩
  · rw [← e, frameLat_isom] at hx
    exact Submodule.map_mono h.1 hx
  · obtain ⟨c, -, rfl⟩ := (Iota.mem_frameLat _ _).1 hx
    exact (Iota.mem_span_frameLat _ _).2 ⟨_, Matrix.mulVec_mulVec _ _ _⟩

theorem Transp.symm (hJ : IsUnit J.det) (h : Transp σ J P Λ A Λ' B) : Transp σ J P Λ' B Λ A := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  have l := Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1)
  refine ⟨s⁻¹, inS_inv hJ hs, by rw [← latMap_mul, l, latMap_one], u⁻¹, UO_inv hu, ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, up_mul_inv hu.1, Matrix.mul_one, ← Matrix.mul_assoc, l, Matrix.one_mul]

theorem Transp.trans (h : Transp σ J P Λ A Λ' B) (k : Transp σ J P Λ' B Λ'' C) : Transp σ J P Λ A Λ'' C := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  obtain ⟨t, ht, rfl, v, hv, rfl⟩ := k
  exact ⟨t * s, inS_mul ht hs, latMap_mul _ _ _, u * v, UO_mul hu hv, by simp only [Matrix.mul_assoc]⟩

theorem move_equivalence (hJ : IsUnit J.det) : Equivalence (Move σ J Λ P) := by
  refine ⟨fun A => ⟨1, ⟨inN_one, latMap_one _⟩, 1, one_mem_UO, by simp⟩, ?_, ?_⟩
  · rintro A _ ⟨s, ⟨hs, e⟩, u, hu, rfl⟩
    have l := Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1)
    refine ⟨s⁻¹, ⟨inN_inv hJ hs, by conv_lhs => rw [← e, ← latMap_mul, l, latMap_one]⟩, u⁻¹, UO_inv hu, ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, up_mul_inv hu.1, Matrix.mul_one, ← Matrix.mul_assoc, l,
      Matrix.one_mul]
  · rintro A _ _ ⟨s, ⟨hs, e⟩, u, hu, rfl⟩ ⟨t, ⟨ht, f⟩, v, hv, rfl⟩
    exact ⟨t * s, ⟨inN_mul ht hs, by rw [latMap_mul, e, f]⟩, u * v, UO_mul hu hv, by
      simp only [Matrix.mul_assoc]⟩

theorem Move.transp (hP : IsFrame σ J T P) (h : Move σ J Λ P A B) : Transp σ J P Λ A Λ B := by
  obtain ⟨s, hs, u, hu, e⟩ := h
  exact ⟨s, inS_of_inN hP hs.1, hs.2, u, hu, e⟩

theorem Transp.adm (hJ : IsUnit J.det) (hP : Free P) (h1 : PrimIn (frameLat P) Λ) (h2 : PrimIn (frameLat P) Λ')
    (h : Transp σ J P Λ A Λ' B) (hA : admitted σ J T' g Λ P A) : admitted σ J T' g Λ' P B := by
  obtain ⟨s, hs, rfl, u, hu, rfl⟩ := h
  obtain ⟨a, ha, e⟩ := exists_UO hP h1 h2 hs
  obtain ⟨⟨k1, k2⟩, w, hw, k3⟩ := hA
  refine ⟨⟨isFrame_mul (isFrame_isom hJ k1 hs.1) hu.1, ?_⟩, a * w * u, UO_mul (UO_mul ha hw) hu, ?_⟩
  · rwa [frameLat_mul hu, frameLat_isom, primIn_latMap (isUnit_det_of_isUn hJ hs.1)]
  · have : (g : E)⁻¹ • (s * A * u - P * (a * w * u)) = s * ((g : E)⁻¹ • (A - P * w)) * u := by
      rw [← Matrix.mul_assoc P, ← Matrix.mul_assoc P, ← e]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [Cong, this, frameLat_mul hu, frameLat_isom]
    exact Submodule.map_mono k3

end Lattice

end GlobalTheory.IntTerm
