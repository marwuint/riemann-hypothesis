import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped TensorProduct

section Adelic

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]

def cjF : E →ₐ[F] E :=
  { (IsCMField.complexConj E : E →+* E) with
    commutes' := fun x => by
      have h : algebraMap F E x ∈ maximalRealSubfield E := by
        rw [mem_maximalRealSubfield_iff]
        intro φ
        exact RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F E))) x
      exact (IsCMField.complexConj E).commutes ⟨_, h⟩ }

abbrev Af : Type := FiniteAdeleRing (𝓞 F) F

abbrev Ai : Type := InfiniteAdeleRing F

structure HSpace (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) where
  Gm : Matrix (Fin r) (Fin r) E
  Gm_herm : ∀ a b, cc (Gm a b) = Gm b a
  Gm_det : Gm.det ≠ 0
  L : Submodule (𝓞 E) (Fin r → E)
  L_fg : L.FG
  L_span : Submodule.span E (L : Set (Fin r → E)) = ⊤
  L_dual : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gm x y)

def HSpace.std (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) : HSpace E r where
  Gm := 1
  Gm_herm a b := by by_cases h : a = b <;> simp [cc, Matrix.one_apply, h, eq_comm]
  Gm_det := by simp
  L := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
  L_fg := Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  L_span := by
    refine eq_top_iff.2 fun x _ => ?_
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (x i) : Fin r → E) = x i • (Pi.single i 1 : Fin r → E) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span fun k _ => ?_)
    by_cases h : k = i
    · subst h; simpa using Submodule.one_le.1 le_rfl
    · simp [h]
  L_dual x := by
    have hi : ∀ z : E, z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := fun z => by
      rw [Submodule.mem_one]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
    have hh : ∀ y, herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * cc (y a) := fun y => by
      simp [herm, Matrix.one_apply]
    constructor
    · intro hx y hy
      rw [hh]
      refine IsIntegral.sum _ fun a _ => ((hi _).1 (hx a trivial)).mul ?_
      exact ((hi _).1 (hy a trivial)).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
    · intro h a _
      have := h (Pi.single a 1) fun k _ => by
        by_cases hk : k = a
        · subst hk; simpa using Submodule.one_le.1 le_rfl
        · simp [hk]
      rw [hh, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc]) (by simp)] at this
      exact (hi _).2 (by simpa [cc] using this)

variable {r : ℕ}

variable (A : Type) [CommRing A] [Algebra F A]

def incl : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom

def hermA (V : HSpace E r) (x y : Fin r → A ⊗[F] E) : A ⊗[F] E :=
  ∑ a, ∑ b, x a * incl F A (V.Gm a b) * Algebra.TensorProduct.map (AlgHom.id F A) (cjF F) (y b)

def UA (V : HSpace E r) : Subgroup (GL (Fin r) (A ⊗[F] E)) where
  carrier := {g | ∀ x y, hermA F A V (g.val.mulVec x) (g.val.mulVec y) = hermA F A V x y}
  one_mem' := fun x y => by simp
  mul_mem' := fun {g h} hg hh x y => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hh]
  inv_mem' := fun {g} hg x y => by
    rw [← hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.one_mulVec]

abbrev GA (V : HSpace E r) : Type := UA F (Ai F) V × UA F (Af F) V

def IsRat (V : HSpace E r) (γ : GL (Fin r) E) (g : GA F V) : Prop :=
  g.1.1.val = γ.val.map (incl F (Ai F)) ∧ g.2.1.val = γ.val.map (incl F (Af F))

def latHat (L : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → Af F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ L, z = fun i => a ⊗ₜ[F] x i}

def levelK (V : HSpace E r) (N : ℕ) : Subgroup (GA F V) where
  carrier := {k | k.1 = 1 ∧ (∀ z, z ∈ latHat F V.L ↔ k.2.1.val.mulVec z ∈ latHat F V.L) ∧
    ∀ z ∈ latHat F V.L, ∃ w ∈ latHat F V.L, k.2.1.val.mulVec z - z = N • w}
  one_mem' := ⟨rfl, fun z => by simp, fun z _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    have e : ∀ z, (g * h).2.1.val.mulVec z = g.2.1.val.mulVec (h.2.1.val.mulVec z) := fun z => by
      rw [Matrix.mulVec_mulVec]; rfl
    refine ⟨by rw [Prod.fst_mul, g1, h1, mul_one], fun z => by rw [e, ← g2, ← h2], fun z hz => ?_⟩
    obtain ⟨w, hw, e1⟩ := h3 z hz
    obtain ⟨w', hw', e2⟩ := g3 _ ((h2 z).1 hz)
    exact ⟨w' + w, add_mem hw' hw, by rw [e, smul_add, ← e1, ← e2]; abel⟩
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    have e : ∀ z, g.2.1.val.mulVec ((g⁻¹).2.1.val.mulVec z) = z := fun z => by
      rw [Matrix.mulVec_mulVec]
      have : g.2.1.val * (g⁻¹).2.1.val = 1 := Units.mul_inv _
      rw [this, Matrix.one_mulVec]
    have s : ∀ z, z ∈ latHat F V.L ↔ (g⁻¹).2.1.val.mulVec z ∈ latHat F V.L := fun z => by
      rw [g2 ((g⁻¹).2.1.val.mulVec z), e]
    refine ⟨by rw [Prod.fst_inv, g1, inv_one], s, fun z hz => ?_⟩
    obtain ⟨w, hw, e1⟩ := g3 _ ((s z).1 hz)
    exact ⟨-w, neg_mem hw, by rw [smul_neg, ← e1, e]; abel⟩

def latAt (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (V : HSpace E r) (g : UA F (Af F) V) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ x : Fin r → E,
    (∃ z ∈ latHat F V.L, (fun i => incl F (Af F) (x i)) = g.1.val.mulVec z) ∧ v = a • x}

end Adelic

structure Nums (E : Type) [Field E] [NumberField E] where
  k : ℕ
  m : ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  Nc : ℕ
  Nc_pos : 0 < Nc
  AA : FractionalIdeal (nonZeroDivisors (𝓞 E)) E
  Os : Subring ℂ

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Nums.r (R : Nums E) : ℕ := R.k + R.m - 1

abbrev Nums.J (R : Nums E) : Type := {j : ℕ // 1 ≤ j ∧ j ≤ R.m}

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F E]

structure CorePar (R : Nums E) : Type 1 where
  H : Host E
  l : Level H
  c : Coeff l
  Dw : R.J → Datum H
  Xo : ∀ j, Moduli (Dw j) l

  U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ R.r

  V : R.J → HSpace E R.r

  dict : ∀ j (σ : c.F →+* ℂ), GoodEmb c σ → GA F (V j) → Σ k, Frame ((U j σ).X k).Ψ R.r

  mu : ∀ j (σ : c.F →+* ℂ), GoodEmb c σ → GA F (V j) → ℂ

  Kf : ∀ j, Subgroup (GA F (V j))

  pi : Fin 2 → 𝓞 E

namespace CorePar

variable {F} {R : Nums E} (Q : CorePar F R)

def sg0 : Q.c.F →+* ℂ := Q.c.F.val.toRingHom

theorem base_embedding_good : GoodEmb Q.c Q.sg0 := rfl

end CorePar

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm
