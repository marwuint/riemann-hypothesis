import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticLatticeForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelB

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate

noncomputable section

namespace TX

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open Classical in

def dimT (σ : E →+* ℂ) : ℕ := if σ ∈ X.Ψ then X.p0 else r - X.p0

theorem dimT_of_notMem {σ : E →+* ℂ} (h : σ ∉ X.Ψ) : dimT X σ = r - X.p0 := by
  classical
  simp [dimT, h]

theorem dimT_le (σ : E →+* ℂ) : dimT X σ ≤ r := by
  classical
  unfold dimT; split_ifs
  · exact X.p0_le
  · omega

def psiOf (σ : E →+* ℂ) (h : σ ∉ X.Ψ) : X.Ψ := ⟨ComplexEmbedding.conjugate σ, (X.conj_mem_iff σ).mpr h⟩

theorem hermC_add_left (τ : E →+* ℂ) (u u' v : Fin r → ℂ) :
    hermC τ X.Gm (u + u') v = hermC τ X.Gm u v + hermC τ X.Gm u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hermC_smul_left (τ : E →+* ℂ) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ X.Gm (c • u) v = c * hermC τ X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

variable (e : X.Ψ → Fin r → (Fin r → ℂ))

theorem neg_lt (σ : E →+* ℂ) (h : σ ∉ X.Ψ) (a : Fin (dimT X σ)) : X.p0 + a.1 < r := by
  have h1 := dimT_of_notMem X h
  have := a.2; have := X.p0_le; omega

open Classical in

def coordF (u : X.Ψ → Fin r → ℂ) (i : Idx (dimT X)) : ℂ :=
  if h : i.1 ∈ X.Ψ then
    (Real.sqrt (X.c ⟨i.1, h⟩) : ℂ) *
      hermC i.1 X.Gm (u ⟨i.1, h⟩) (e ⟨i.1, h⟩ ⟨i.2.1, lt_of_lt_of_le i.2.2 (dimT_le X i.1)⟩)
  else
    (Real.sqrt (X.c (psiOf X i.1 h)) : ℂ) *
      conj (-hermC (psiOf X i.1 h).1 X.Gm (u (psiOf X i.1 h))
        (e (psiOf X i.1 h) ⟨X.p0 + i.2.1, neg_lt X i.1 h i.2⟩))

def Lc : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] Vsp (dimT X) where
  toFun u := WithLp.toLp 2 (coordF X e u)
  map_add' u u' := by
    ext i
    simp only [coordF, Pi.add_apply, WithLp.toLp_add, PiLp.add_apply]
    split_ifs <;> simp [hermC_add_left, mul_add] <;> ring
  map_smul' c u := by
    ext i
    simp only [coordF, Pi.smul_apply, RingHom.id_apply, PiLp.smul_apply, WithLp.toLp_smul]
    have hc : ∀ w : Fin r → ℂ, c • w = (c : ℂ) • w := fun w => rfl
    split_ifs
    · rw [hc, hermC_smul_left]; simp [Complex.real_smul]; ring
    · rw [hc, hermC_smul_left]; simp [Complex.real_smul]; ring

variable {X e}

variable (X e) in

def phi : (Fin r → E) →+ Vsp (dimT X) where
  toFun v := Lc X e (X.embV v)
  map_zero' := by
    have : X.embV (0 : Fin r → E) = 0 := by funext τ a; simp [Data.embV, Data.emb]
    rw [this, map_zero]
  map_add' u v := by
    have : X.embV (u + v) = X.embV u + X.embV v := by funext τ a; simp [Data.embV, Data.emb]
    rw [this, map_add]

theorem phi_apply (v : Fin r → E) : phi X e v = Lc X e (X.embV v) := rfl

end TX

end

end ReciprocityTheory.ChartRestriction.G.I2
