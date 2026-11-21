import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemLatGHat
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelUnip

theorem pow_apply_eq_zero {R : Type} [CommRing R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (hN : ∀ i j : Fin n, (j : ℕ) ≤ i → N i j = 0) :
    ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) < i + k → (N ^ k) i j = 0 := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    intro h; subst h; omega
  | succ k ih =>
    intro i j hij
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) ≤ i
    · rw [hN i l hl, zero_mul]
    · rw [ih l j (by omega), mul_zero]

theorem sub_one_pow_eq_zero' {κ : Type} [CommRing κ] {n : ℕ} (X : Matrix (Fin n) (Fin n) κ)
    (h0 : ∀ i j : Fin n, (j : ℕ) < i → X i j = 0) (h1 : ∀ i, X i i = 1) : (X - 1) ^ n = 0 := by
  have hN : ∀ i j : Fin n, (j : ℕ) ≤ i → (X - 1) i j = 0 := by
    intro i j hij
    rcases Nat.lt_or_eq_of_le hij with h | h
    · have h' : j ≠ i := fun e => by subst e; omega
      rw [Matrix.sub_apply, Matrix.one_apply_ne h'.symm, h0 i j h, sub_zero]
    · have e : j = i := Fin.ext h
      subst e
      rw [Matrix.sub_apply, Matrix.one_apply_eq, h1 j, sub_self]
  ext i j
  rw [pow_apply_eq_zero _ hN n i j (by omega), Matrix.zero_apply]

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_matrix_pow (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y : GL (Fin n) (Formalism.L2.Herm.intAf F E)} {r : ℕ}
    (h : ∀ P ∈ T, (((Formalism.UG.bc (resS F P) y : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r = 0)
    {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E), oToS F E b • ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j) = M • c := by
    intro i j
    have h0 : ∀ P ∈ T, resS F P ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j) = resS F P 0 := by
      intro P hP
      have e : (resS F P).mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) =
          (((Formalism.UG.bc (resS F P) y : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r := by
        rw [map_pow, map_sub, map_one]; rfl
      have := congrFun (congrFun (e.trans (h P hP)) i) j
      rw [map_zero]
      exact this
    have h1 : (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) := by
      have := GlobalTheory.LevelUnique.mem_map_prod (oToS F E) T fun P hP => GlobalTheory.LevelUnique.sub_mem_idS (h0 P hP)
      simpa using this
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => by rw [Matrix.smul_apply, smul_eq_mul, hc i j]; rfl⟩

end Res

theorem keeps_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, (β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), K *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have hN := fun z hz => (hfr _).2 (GlobalTheory.LevelUnique.conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at hN hK
  intro z hz
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
  convert h4 using 1
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.symm_apply_apply, hK]

theorem exists_pow_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) {r : ℕ}
    (h : ∀ P ∈ T, (((redFn β P x : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) - 1) ^ r = 0) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - 1) ^ r = M • N := by
  obtain ⟨y, rfl⟩ := hx
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix_pow T hJ h hb
  have e0 : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) * (β⁻¹).1 := rfl
  have e2 : (((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r =
      β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) * (β⁻¹).1 := by
    have e1 : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
        β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) * (β⁻¹).1 := by
      rw [e0, map_sub, map_one, mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [e1, Units.conj_pow, map_pow]
  have e4 : ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) •
      (Formalism.L2.Herm.intAf F E).subtype.mapMatrix (((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) ^ r) =
      M • (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s := by
    ext i j
    have := congrArg (fun m : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => (Formalism.L2.Herm.intAf F E).subtype (m i j)) hs
    simp only [Matrix.smul_apply, map_nsmul, smul_eq_mul, map_mul] at this
    simpa [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul] using this
  have e3 : ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) •
      ((((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r) =
      M • (β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s * (β⁻¹).1) := by
    rw [e2, ← smul_mul_assoc, ← mul_smul_comm, e4, mul_smul_comm, smul_mul_assoc]
  refine ⟨(β.1 * (Formalism.L2.Herm.intAf F E).subtype.mapMatrix s * (β⁻¹).1).map (Algebra.TensorProduct.comm F _ E).symm,
    keeps_hat hfr s (fun i j => by rw [Matrix.map_apply, AlgEquiv.apply_symm_apply]; rfl), Matrix.ext fun i j => ?_⟩
  apply (Algebra.TensorProduct.comm F _ E).injective
  have hm : ((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (Algebra.TensorProduct.comm F _ E).toRingHom.mapMatrix K := Matrix.ext fun i j => hK i j
  have hpow : ((((frGL β y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) ^ r) i j =
      Algebra.TensorProduct.comm F _ E (((K - 1) ^ r) i j) := by
    rw [hm, ← map_one (Algebra.TensorProduct.comm F _ E).toRingHom.mapMatrix, ← map_sub, ← map_pow]
    rfl
  rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
    ← hpow]
  exact congrFun (congrFun e3 i) j

variable {D : D7}

theorem sub_one_mulVec_mem {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {k : GA D V} (hk : Lev.finE V k ∈ St β) :
    ∀ z ∈ latGHat V 1, ((finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) - 1) *ᵥ z ∈ latGHat V 1 := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ := hk
  have hN : ∀ z ∈ latHat V, (finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) *ᵥ z ∈ latHat V := by
    rw [hl]
    exact keeps_hat hfr (y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
      (fun i j => by
        have := congrArg (fun x : GL (Fin V.rank) (Lev.EAf D) => (x : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j) hy
        exact this)
  intro z hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_mem (GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz) hz

theorem exists_pow_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V} (hk : Lev.finE V k ∈ St β) {r : ℕ}
    (h : ∀ P ∈ T, (((redFn β P (Lev.finE V k) : GL (Fin V.rank) (kP P)) : Matrix (Fin V.rank) (Fin V.rank) (kP P)) - 1) ^ r = 0)
    {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) •
        ((((finHom V k : Matrix (Fin V.rank) (Fin V.rank) _) - 1) ^ r) *ᵥ z -
          (0 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ z) = M • w := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_pow_hat hfr T hJ hk h hb (K := (finHom V k : Matrix (Fin V.rank) (Fin V.rank) _))
    (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [Matrix.zero_mulVec, sub_zero, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem step {R : Type} [CommRing R] {n : ℕ} (K P : Matrix (Fin n) (Fin n) R) (y₀ y₁ v w₁ w₂ : Fin n → R) (M : ℕ)
    (e₁ : y₁ - K *ᵥ y₀ = M • w₁) (e₂ : y₀ - P *ᵥ v = M • w₂) :
    (y₁ - y₀) - ((K - 1) * P) *ᵥ v = M • (w₁ + (K - 1) *ᵥ w₂) := by
  have e₂' := eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp e₂).symm
  have e₁' := sub_eq_iff_eq_add.mp e₁
  rw [← Matrix.mulVec_mulVec, e₂', e₁', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, smul_add]
  abel

theorem approx_pow {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    {K : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (hK : ∀ z ∈ latGHat V 1, (K - 1) *ᵥ z ∈ latGHat V 1) {f : La →ₗ[𝓞 D.host.E] La}
    (hf : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w) :
    ∀ n : ℕ, ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (((f - 1) ^ n) a)) - ((K - 1) ^ n) *ᵥ finVec V (ι a) = M • w := by
  have hm : ∀ a, finVec V (ι a) ∈ latGHat V 1 := fun a =>
    (GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hι.2 ▸ LinearMap.mem_range_self ι a)
  have hJ : ∀ (g : La →ₗ[𝓞 D.host.E] La) a, a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) →
      g a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) := by
    intro g a ha
    have : g a ∈ (J • (⊤ : Submodule (𝓞 D.host.E) La)).map g := Submodule.mem_map_of_mem ha
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  intro n
  induction n with
  | zero =>
    intro a _
    exact ⟨0, zero_mem _, by rw [pow_zero, pow_zero, Matrix.one_mulVec, Module.End.one_apply, sub_self, smul_zero]⟩
  | succ n ih =>
    intro a ha
    obtain ⟨w₂, hw₂, e₂⟩ := ih a ha
    obtain ⟨w₁, hw₁, e₁⟩ := hf _ (hJ ((f - 1) ^ n) a ha)
    refine ⟨w₁ + (K - 1) *ᵥ w₂, add_mem hw₁ (hK _ hw₂), ?_⟩
    have ex : ((f - 1) ^ (n + 1)) a = f (((f - 1) ^ n) a) - ((f - 1) ^ n) a := by
      rw [pow_succ', Module.End.mul_apply]; rfl
    have hsub : ∀ u v : Fin V.rank → D.host.E, finVec V (u - v) = finVec V u - finVec V v := fun u v => by
      funext i; simp [finVec, TensorProduct.tmul_sub]
    rw [ex, pow_succ', map_sub ι, hsub]
    exact step _ _ _ _ _ _ _ _ e₁ e₂

end GlobalTheory.LevelUnip

