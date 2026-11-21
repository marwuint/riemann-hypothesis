import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Relab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ)

theorem relab_inj : Function.Injective (relab c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem relab_rt (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
  have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
  · refine ⟨fun _ => hx, fun _ => ?_⟩
    rw [hval, ← hσ0]
    exact congrArg σ (Subtype.ext hx)
  · have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
      rw [← map_neg]
      exact congrArg σ (Subtype.ext hx)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      rw [← hval, h, hσ0] at h1
      exact h0 (by linear_combination h1 / 2)
    · exfalso
      exact h0 (by linear_combination (h.symm.trans hx) / 2)

def relabE : (E →+* ℂ) ≃ (E →+* ℂ) :=
  Equiv.ofBijective (relab c σ) (Finite.injective_iff_bijective.mp (relab_inj c σ))

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun a => Complex.conj_conj _

theorem conjugate_eq (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ = conjEmb τ := rfl

def conjE : (E →+* ℂ) ≃ (E →+* ℂ) :=
  ⟨conjEmb, conjEmb, conjEmb_conjEmb, conjEmb_conjEmb⟩

end Relab

section Letters

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem conj_mem_iff {X : Data E r} (ρ : E →+* ℂ) : conjEmb ρ ∈ X.Ψ ↔ ρ ∉ X.Ψ := by
  have := X.cmType (conjEmb ρ)
  rw [conjugate_eq, conjEmb_conjEmb] at this
  exact this

include hU in
theorem dim_of (ρ : E →+* ℂ) :
    A.T.dim ρ = if ρ ∈ (U.X k).Ψ then (U.X k).p0 else r - (U.X k).p0 := by
  split_ifs with h
  · exact A.dim_pos ⟨ρ, h⟩
  · have hc : conjEmb ρ ∈ (U.X k).Ψ := (conj_mem_iff ρ).mpr h
    have := A.dim_neg ⟨conjEmb ρ, hc⟩
    rwa [conjugate_eq, conjEmb_conjEmb] at this

include hU hσ in
theorem mult_of (ρ : E →+* ℂ) :
    Dw.mult ((relabE c σ).symm (conjEmb ρ)) = if ρ ∈ (U.X k).Ψ then (U.X k).p0 else r - (U.X k).p0 := by
  have hrel : relab c σ ((relabE c σ).symm (conjEmb ρ)) = conjEmb ρ := (relabE c σ).apply_symm_apply _
  have hiff : ((relabE c σ).symm (conjEmb ρ)) (H.rt : E) = H.rt0 ↔ ρ ∉ (U.X k).Ψ := by
    rw [← relab_rt c σ hσ, hrel, ← (hU.2.1 k).2, conj_mem_iff]
  have hr := hU.1
  unfold Datum.mult
  rw [(hU.2.1 k).1]
  split_ifs with h1 h2 h2
  · exact absurd h2 (hiff.mp h1)
  · omega
  · rfl
  · exact absurd (hiff.mpr h2) h1

include hU hσ in

def fibE (ρ : E →+* ℂ) : Fin (A.T.dim ρ) ≃ Fin (Dw.mult ((relabE c σ).symm (conjEmb ρ))) :=
  if h : ρ ∈ (U.X k).Ψ then
    (finCongr (by rw [dim_of hU A, if_pos h])).trans
      (Fin.revPerm.trans (finCongr (by rw [mult_of hU hσ, if_pos h])))
  else finCongr (by rw [dim_of hU A, mult_of hU hσ, if_neg h])

include hU hσ in

def letT : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim ≃ Fin W.g :=
  (Equiv.sigmaCongr ((conjE).trans (relabE c σ).symm) (fun ρ => fibE hU hσ A ρ)).trans W.e.symm

end Letters

section Map

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

def yf (τ : (U.X k).Ψ) (b : Fin r) : ℂ :=
  (sgn (U.X k).p0 b : ℂ) * hermC τ.1 (U.X k).Gm (A.e τ b) (col (mat x.1 τ) b)

include hU in
theorem index_lt_signature_of_mem {ρ : E →+* ℂ} (h : ρ ∈ (U.X k).Ψ) (a : Fin (A.T.dim ρ)) : (a : ℕ) < (U.X k).p0 := by
  have h1 := dim_of hU A ρ
  rw [if_pos h] at h1
  have := a.2
  omega

include hU in
theorem index_lt_complementSignature_of_not_mem {ρ : E →+* ℂ} (h : ρ ∉ (U.X k).Ψ) (a : Fin (A.T.dim ρ)) : (a : ℕ) < r - (U.X k).p0 := by
  have h1 := dim_of hU A ρ
  rw [if_neg h] at h1
  have := a.2
  omega

include hU in

def wt (i : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) : ℂ :=
  if h : i.1 ∈ (U.X k).Ψ then
    (Real.sqrt ((U.X k).c ⟨i.1, h⟩) : ℂ) *
      conj (yf A ⟨i.1, h⟩ ⟨i.2, lt_of_lt_of_le (index_lt_signature_of_mem hU A h i.2) (U.X k).p0_le⟩)
  else
    (Real.sqrt ((U.X k).c ⟨conjEmb i.1, (conj_mem_iff _).mpr h⟩) : ℂ) *
      yf A ⟨conjEmb i.1, (conj_mem_iff _).mpr h⟩
        ⟨(U.X k).p0 + i.2, by have := index_lt_complementSignature_of_not_mem hU A h i.2; have := (U.X k).p0_le; omega⟩

include hU hσ in

def Lmap : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim where
  toFun z := WithLp.toLp 2 fun i => wt hU A i * z (letT hU hσ W A i)
  map_add' z z' := by
    ext i
    simp [mul_add]
  map_smul' a z := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.toLp_apply, PiLp.smul_apply]
    ring

theorem Lmap_apply (z : Fin W.g → ℂ) (i : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) :
    Lmap hU hσ W A z i = wt hU A i * z (letT hU hσ W A i) := rfl

end Map

end ReciprocityTheory.ChartRestriction.G.PullbackSections
