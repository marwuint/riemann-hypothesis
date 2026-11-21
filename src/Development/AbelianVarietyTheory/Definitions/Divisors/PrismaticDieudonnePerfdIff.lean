import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.PerfdLat

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

structure PrismData (p : ℕ) [Fact p.Prime] : Type 1 where

  M : ∀ S : CycPerfd p, PDivGroup p S.R → ModuleCat.{0} (Ainf p S.R)

  map : ∀ (S : CycPerfd p) (G H : PDivGroup p S.R), (G ⟶ H) →+ (M S H →ₗ[Ainf p S.R] M S G)

  φ : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G →ₛₗ[(frobenius : Ainf p S.R →+* Ainf p S.R)] M S G

  lie : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G →ₛₗ[fontaineTheta S.R p] G.dual.Lie

  du : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G.dual ≃ₗ[Ainf p S.R] Module.Dual (Ainf p S.R) (M S G)

  l : ∀ S : CycPerfd p, M S (PDivGroup.mu p S.R)

  e : ∀ S : CycPerfd p, M S (const p S.R)

  projective : ∀ S G, Module.Projective (Ainf p S.R) (M S G)

  finite : ∀ S G, Module.Finite (Ainf p S.R) (M S G)

  rank_eq : ∀ S G q, Module.rankAtStalk (R := Ainf p S.R) (M S G) q = G.height

  exists_φ_eq : ∀ S G m, ∃ n, φ S G n = frobenius (xi S.ε) • m

  lie_projective : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), Module.Projective S.R G.dual.Lie

  lie_finite : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), Module.Finite S.R G.dual.Lie

  lie_surjective : ∀ S G, Function.Surjective (lie S G)

  lie_eq_zero_iff : ∀ S G m, lie S G m = 0 ↔ ∃ n, φ S G m = frobenius (xi S.ε) • n

  map_id : ∀ S G, map S G G (𝟙 G) = LinearMap.id

  map_comp : ∀ S G H K (f : G ⟶ H) (g : H ⟶ K), map S G K (f ≫ g) = map S G H f ∘ₗ map S H K g

  map_φ : ∀ S G H (f : G ⟶ H) (m : M S H), map S G H f (φ S H m) = φ S G (map S G H f m)

  lie_map : ∀ S G H (f : G ⟶ H) (m : M S H),
    lie S G (map S G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie S H m)

  du_map : ∀ S G H (f : G ⟶ H) (m : M S H) (x : M S G.dual),
    du S H (map S H.dual G.dual (dualHom G H f) x) m = du S G x (map S G H f m)

  l_bijective : ∀ S, Function.Bijective (LinearMap.toSpanSingleton (Ainf p S.R) _ (l S))

  e_bijective : ∀ S, Function.Bijective (LinearMap.toSpanSingleton (Ainf p S.R) _ (e S))

  φ_l : ∀ S, φ S _ (l S) = frobenius (xi S.ε) • l S

  φ_e : ∀ S, φ S _ (e S) = e S

  map_eps : ∀ S, map S _ _ (epsHom (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε)) (l S) = Sandwich.mu S.ε • e S

  du_e_l : ∀ S, du S (PDivGroup.mu p S.R) (e S) (l S) = 1

  baseChange : ∀ (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R), S.Over S' α →
    ∃ bc : ∀ G : PDivGroup p S.R, M S G →ₛₗ[α] M S' (G.baseChange S'.R),
      (∀ G, Submodule.span (Ainf p S'.R) (Set.range (bc G)) = ⊤ ∧ ∀ m, bc G (φ S G m) = φ S' _ (bc G m)) ∧
      (∀ (G H : PDivGroup p S.R) (f : G ⟶ H) (m : M S H),
        bc G (map S G H f m) = map S' _ _ (baseChangeMap S'.R f) (bc H m)) ∧
      ∀ j : PDivGroup.mu p S'.R ⟶ (PDivGroup.mu p S.R).baseChange S'.R,
        (∀ n, j.app n (1 ⊗ₜ AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1) →
          map S' _ _ j (bc _ (l S)) = l S'

attribute [instance] PrismData.projective PrismData.finite

section Const

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

structure ConstTate (ε : (PDivGroup.mu p O).Tate) (G : PDivGroup p O) : Type where

  t : Fin G.height → G.Tate

  t' : Fin G.height → G.dual.Tate

  pair : ∀ i j, pairing G O (t i) (t' j) = if i = j then ε else 0

theorem pairing_bidual (G : PDivGroup p O) (t : G.Tate) (χ : G.dual.Tate) :
    pairing G.dual O χ (tateCongr O G.bidual t) = pairing G O t χ :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing, ← charHom_app_muT]
    change χ.pt n ((dualChar G t).app n _) = _
    rw [dualChar_app_muT, ← apply_charElem]
    rfl

section BaseChange

variable (O' : Type) [CommRing O'] [Algebra O O'] {G : PDivGroup p O}

theorem baseChange_mulP (G : PDivGroup p O) (n : ℕ) : (G.baseChange O').mulP n = PDiv.bcMap O' (G.mulP n) :=
  PDiv.bc_hom_ext fun a => by
    obtain ⟨b, rfl⟩ := G.res_surjective n a
    have h := map_nsmul (AddMonoidHom.mk' (baseChangeMap (G := G) (H := G) O') (baseChangeMap_add O')) p (𝟙 G)
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul ℤ_[p]] at h
    have h1 : baseChangeMap O' ((p : ℤ_[p]) • 𝟙 G) = (p : ℤ_[p]) • 𝟙 (G.baseChange O') :=
      h.trans (congrArg _ ((baseChangeFunctor p O O').map_id G))
    have h2 := congrArg (fun f => Hom.app f (n + 1) (1 ⊗ₜ b)) h1
    simp only [baseChangeMap_app, natCast_smul_id_app] at h2
    rw [PDiv.bcMap_tmul, mulP_res]
    exact ((G.baseChange O').mulP_res n (1 ⊗ₜ b)).trans h2.symm

def bcTate (t : G.Tate) : (G.baseChange O').Tate :=
  ⟨fun n => Algebra.TensorProduct.lift (AlgHom.id O' O') ((Algebra.ofId O O').comp (t.pt n)) fun _ _ => .all _ _,
    fun n => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => by
      rw [baseChange_mulP]
      simp [t.pt_mulP])⟩

@[simp] theorem bcTate_pt (t : G.Tate) (n : ℕ) (r : O') (a : G.A n) :
    (bcTate O' t).pt n (r ⊗ₜ a) = r * algebraMap O O' (t.pt n a) := rfl

omit [Fact p.Prime] in

theorem isGroupLikeElem_one_tmul (χ : G.dual.Tate) (n : ℕ) :
    IsGroupLikeElem O' ((1 : O') ⊗ₜ[O] charElem χ n) where
  counit_eq_one := by simp [(isGroupLikeElem_charElem χ n).counit_eq_one]
  comul_eq_tmul_self := by
    simp [TensorProduct.comul_tmul, (isGroupLikeElem_charElem χ n).comul_eq_tmul_self]

def bcChar (χ : G.dual.Tate) : (G.baseChange O').dual.Tate :=
  ⟨fun n => evalPoint _ (isGroupLikeElem_one_tmul O' χ n), fun n => AlgHom.ext fun φ => by
    change ((G.baseChange O').dual.mulP n φ) ((1 : O') ⊗ₜ[O] charElem χ (n + 1)) = φ.ofConv (1 ⊗ₜ charElem χ n)
    rw [dual_mulP, CartierDual.map_apply, ← res_charElem χ n]
    rfl⟩

@[simp] theorem charElem_bcChar (χ : G.dual.Tate) (n : ℕ) : charElem (bcChar O' χ) n = 1 ⊗ₜ charElem χ n :=
  CartierDual.eq_of_forall_apply (R := O') fun φ => apply_charElem _ n φ

theorem muRoot_pairing_bc (t : G.Tate) (χ : G.dual.Tate) (n : ℕ) :
    muRoot (pairing _ O' (bcTate O' t) (bcChar O' χ)) n = algebraMap O O' (muRoot (pairing G O t χ) n) := by
  rw [muRoot_pairing, muRoot_pairing, charElem_bcChar, bcTate_pt, one_mul]

theorem tateMap_bcTate {H : PDivGroup p O} (f : G ⟶ H) (t : G.Tate) :
    tateMap _ _ O' (baseChangeMap O' f) (bcTate O' t) = bcTate O' (tateMap G H O f t) :=
  TateOver.ext (funext fun _ => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun _ => rfl))

def dualBaseChange (G : PDivGroup p O) : (G.baseChange O').dual ≅ G.dual.baseChange O' where
  hom := ⟨fun n => CartierDual.baseChangeHom O O' (G.A n), fun n => BialgHom.ext fun x => by
    change CartierDual.map ((G.baseChange O').mulP n) _ = _
    rw [baseChange_mulP]
    exact (CartierDual.baseChange_map O' (G.mulP n) x).symm⟩
  inv := ⟨fun n => (CartierDual.baseChange O O' (G.A n)).symm, fun n => BialgHom.ext fun x => by
    obtain ⟨y, rfl⟩ := (CartierDual.baseChange O O' (G.A (n + 1))).surjective x
    change PDiv.bcMap O' (CartierDual.map (G.mulP n)) ((CartierDual.baseChange O O' (G.A (n + 1))).symm
      (CartierDual.baseChange O O' (G.A (n + 1)) y)) = (CartierDual.baseChange O O' (G.A n)).symm
        (CartierDual.map ((G.baseChange O').mulP n) (CartierDual.baseChange O O' (G.A (n + 1)) y))
    rw [baseChange_mulP, PDiv.bcMap, PDiv.bcMap, ← CartierDual.baseChange_map, BialgEquiv.symm_apply_apply,
      BialgEquiv.symm_apply_apply]⟩
  hom_inv_id := hom_ext fun n => BialgHom.ext fun a => (CartierDual.baseChange O O' (G.A n)).apply_symm_apply a
  inv_hom_id := hom_ext fun n => BialgHom.ext fun a => (CartierDual.baseChange O O' (G.A n)).symm_apply_apply a

end BaseChange

namespace ConstTate

variable {ε : (PDivGroup.mu p O).Tate} {G : PDivGroup p O}

def ofPerfect (t : Fin G.height → G.Tate) (t' : Fin G.height → G.dual.Tate) (P : GL (Fin G.height) ℤ_[p])
    (h : ∀ i j, pairing G O (t i) (t' j) = P i j • ε) : ConstTate ε G where
  t := t
  t' j := ∑ k, P⁻¹ k j • t' k
  pair i j := by
    have h1 : ∑ k, P i k * P⁻¹ k j = if i = j then 1 else 0 := by
      have h2 := congrFun (congrFun P.mul_inv i) j
      rwa [Matrix.mul_apply, Matrix.one_apply] at h2
    simp only [map_sum, map_smul, h, smul_smul, mul_comm (P⁻¹ _ j)]
    rw [← Finset.sum_smul, h1]
    split_ifs <;> simp

variable (c : ConstTate ε G)

def dual : ConstTate ε G.dual where
  t := c.t'
  t' i := tateCongr O G.bidual (c.t i)
  pair j i := by rw [pairing_bidual, c.pair]; simp only [eq_comm]

def ofIso {H : PDivGroup p O} (e : G ≅ H) (h : H.height = G.height) : ConstTate ε H where
  t i := tateMap G H O e.hom (c.t (Fin.cast h i))
  t' j := tateMap _ _ O (dualHom H G e.inv) (c.t' (Fin.cast h j))
  pair i j := by
    rw [pairing_tateMap, ← tateMap_comp, ← dualHom_comp, e.hom_inv_id, dualHom_id, tateMap_id, c.pair]
    simp only [Fin.cast_inj]

def toTate : (Fin G.height → ℤ_[p]) →ₗ[ℤ_[p]] G.Tate := Fintype.linearCombination ℤ_[p] c.t

def Stable (f : End G) (ρ : Matrix (Fin G.height) (Fin G.height) ℤ_[p]) : Prop :=
  ∀ i, tateMap G G O f (c.t i) = ∑ k, ρ k i • c.t k

theorem stable_iff (f : End G) (ρ : Matrix (Fin G.height) (Fin G.height) ℤ_[p]) :
    c.Stable f ρ ↔ ∀ x, tateMap G G O f (c.toTate x) = c.toTate (ρ.mulVec x) := by
  constructor
  · intro h x
    simp only [toTate, Fintype.linearCombination_apply, map_sum, map_smul, h _, Finset.smul_sum, smul_smul,
      Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · intro h i
    simpa [toTate, Fintype.linearCombination_apply, Pi.single_apply] using h (Pi.single i 1)

theorem Stable.mul {c : ConstTate ε G} {f g : End G} {ρ σ : Matrix (Fin G.height) (Fin G.height) ℤ_[p]}
    (hf : c.Stable f ρ) (hg : c.Stable g σ) : c.Stable (f * g) (ρ * σ) :=
  (c.stable_iff _ _).2 fun x => by
    rw [← Matrix.mulVec_mulVec, ← (c.stable_iff _ _).1 hf, ← (c.stable_iff _ _).1 hg]
    rfl

def al : (Fin G.height → O) →ₗ[O] G.dual.omega := Fintype.linearCombination O fun i => hodgeTate G (c.t i)

def alDual : G.Lie →ₗ[O] (Fin G.height → O) := LinearMap.pi fun j => Module.Dual.eval O _ (dlog G (c.t' j))

def W : Submodule O (Fin G.height → O) := LinearMap.ker c.al

theorem al_apply (x : Fin G.height → O) : c.al x = ∑ i, x i • hodgeTate G (c.t i) :=
  Fintype.linearCombination_apply ..

@[simp] theorem alDual_apply (x : G.Lie) (j : Fin G.height) : c.alDual x j = x (dlog G (c.t' j)) := rfl

theorem mem_W (x : Fin G.height → O) : x ∈ c.W ↔ c.al x = 0 := Iff.rfl

section BaseChange

variable (O' : Type) [CommRing O'] [Algebra O O']

def baseChange {ε' : (PDivGroup.mu p O').Tate} (h : ∀ n, muRoot ε' n = algebraMap O O' (muRoot ε n)) :
    ConstTate ε' (G.baseChange O') where
  t i := bcTate O' (c.t i)
  t' j := bcChar O' (c.t' j)
  pair i j := muRoot_ext fun n => by
    rw [muRoot_pairing_bc, c.pair]
    split_ifs
    · exact (h n).symm
    · rw [muRoot_zero, muRoot_zero, map_one]

end BaseChange

end ConstTate

end Const

section Lattices

open scoped Pointwise

def piMap {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (ι : Type) : (ι → A) →ₛₗ[σ] (ι → B) where
  toFun x i := σ (x i)
  map_add' x y := funext fun i => map_add σ (x i) (y i)
  map_smul' a x := funext fun i => map_mul σ a (x i)

@[simp] theorem piMap_apply {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (ι : Type) (x : ι → A) (i : ι) :
    piMap σ ι x i = σ (x i) := rfl

variable {p : ℕ} [Fact p.Prime]

section Ring

variable (S : CycPerfd p)

instance thetaSurjective : RingHomSurjective (fontaineTheta S.R p) := ⟨S.surj⟩

def eps : (PDivGroup.mu p S.R).Tate := muTate S.R (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε)

@[simp] theorem muRoot_eps (n : ℕ) : muRoot (eps S) n = zeta S.ε n := muRoot_muTate ..

theorem constHom_eps : constHom _ (eps S) = epsHom (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε) := rfl

def xiN (n : ℕ) : Ainf p S.R := xi (root^[n] S.ε)

theorem zeta_one_sub_one_dvd : zeta S.ε 1 - 1 ∣ (p : S.R) := by
  have h : fontaineTheta S.R p (xi S.ε) = 0 := by
    rw [← RingHom.mem_ker, S.ker_eq]; exact mem_span_singleton_self _
  have h1 : ∑ i ∈ Finset.range p, zeta S.ε 1 ^ i = 0 := by
    simpa [xi, fontaineTheta_teichmuller, zeta] using h
  have h2 : (p : S.R) = -∑ i ∈ Finset.range p, (zeta S.ε 1 ^ i - 1) := by simp [h1]
  rw [h2, dvd_neg]
  exact Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one _ i

theorem zeta_sub_one_dvd (n : ℕ) : zeta S.ε (n + 1) - 1 ∣ zeta S.ε 1 - 1 := by
  induction n with
  | zero => exact dvd_rfl
  | succ n ih => exact (zeta_succ_pow S.ε (n + 1) ▸ sub_one_dvd_pow_sub_one _ p).trans ih

theorem isSMulRegular_zeta_sub_one (n : ℕ) : IsSMulRegular S.R (zeta S.ε (n + 1) - 1) := by
  obtain ⟨a, ha⟩ := (zeta_sub_one_dvd S n).trans (zeta_one_sub_one_dvd S)
  exact IsSMulRegular.of_mul (a := a) (by rw [mul_comm, ← ha]; exact S.reg)

def base (h : ℕ) : Submodule S.R (Fin h → S.R) := (zeta S.ε 1 - 1) • ⊤

theorem mem_base {h : ℕ} (x : Fin h → S.R) : x ∈ base S h ↔ ∃ y, (zeta S.ε 1 - 1) • y = x := by
  simp [base, Submodule.mem_smul_pointwise_iff_exists]

end Ring

variable (D : PrismData p) {S : CycPerfd p}

def PrismData.eCoord (S : CycPerfd p) : D.M S (const p S.R) ≃ₗ[Ainf p S.R] Ainf p S.R :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).symm

@[simp] theorem PrismData.eCoord_smul_e (a : Ainf p S.R) : D.eCoord S (a • D.e S) = a :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).symm_apply_apply a

@[simp] theorem PrismData.eCoord_smul (m : D.M S (const p S.R)) : D.eCoord S m • D.e S = m :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).apply_symm_apply m

abbrev PrismData.Cov (G : PDivGroup p S.R) : Type := D.M S G.dual

variable {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

def coord : D.Cov G →ₗ[Ainf p S.R] (Fin G.height → Ainf p S.R) :=
  LinearMap.pi fun j => (D.eCoord S).toLinearMap ∘ₗ D.map S (const p S.R) G.dual (constHom G.dual (c.t' j))

theorem coord_apply (m : D.Cov G) (j : Fin G.height) :
    coord D c m j = D.eCoord S (D.map S (const p S.R) G.dual (constHom G.dual (c.t' j)) m) := rfl

def K (n : ℕ) : Submodule (Ainf p S.R) (Fin G.height → Ainf p S.R) :=
  Nat.rec (LinearMap.range (coord D c)) (fun _ N => N.comap (piMap frobenius _)) n

theorem K_zero : K D c 0 = LinearMap.range (coord D c) := rfl

theorem K_succ (n : ℕ) : K D c (n + 1) = (K D c n).comap (piMap frobenius _) := rfl

theorem mem_K_zero (x : Fin G.height → Ainf p S.R) : x ∈ K D c 0 ↔ ∃ m, coord D c m = x := Iff.rfl

theorem mem_K_succ (n : ℕ) (x : Fin G.height → Ainf p S.R) :
    x ∈ K D c (n + 1) ↔ piMap frobenius _ x ∈ K D c n := Iff.rfl

def b : D.Cov G →ₛₗ[fontaineTheta S.R p] (Fin G.height → S.R) := (piMap (fontaineTheta S.R p) _).comp (coord D c)

theorem b_apply (m : D.Cov G) (j : Fin G.height) : b D c m j = fontaineTheta S.R p (coord D c m j) := rfl

def thetaK (n : ℕ) : Submodule S.R (Fin G.height → S.R) := (K D c n).map (piMap (fontaineTheta S.R p) _)

def H (n : ℕ) : Submodule S.R (Fin G.height → S.R) :=
  ((zeta S.ε 1 - 1) • thetaK D c (n + 1)).comap (LinearMap.lsmul S.R _ (zeta S.ε (n + 1) - 1))

end Lattices

end GlobalTheory.PerfdLat
