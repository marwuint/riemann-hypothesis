import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BKIntegralToRational

theorem exists_mul_pow_eq {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {p : A}
    (hu : ¬ IsUnit p) (a : FractionRing A) :
    ∃ (x : A) (N : ℕ), a * algebraMap A (FractionRing A) p ^ N = algebraMap A (FractionRing A) x := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd0 hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hu
  obtain ⟨c, hc⟩ : d ∣ p ^ N := hN.dvd.trans (pow_dvd_pow_of_dvd h1 N)
  refine ⟨n * c, N, ?_⟩
  have hd1 : algebraMap A (FractionRing A) d ≠ 0 := by
    simpa using hd0
  rw [← map_pow, hc, map_mul, map_mul]
  field_simp

theorem continuous_div_mk {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [TopologicalSpace O₀] [IsTopologicalRing O₀] (had : IsAdic (IsLocalRing.maximalIdeal O₀))
    [CommRing O'] [IsDomain O'] (ι : O₀ →+* O') {d : O₀} (hd : d ≠ 0) (hd' : ι d ≠ 0) :
    Continuous fun x : O₀ => (Submodule.Quotient.mk (algebraMap O' (FractionRing O') (ι x) /
      algebraMap O' (FractionRing O') (ι d)) : KmodO O') := by
  have hd1 : algebraMap O' (FractionRing O') (ι d) ≠ 0 := by simpa using hd'
  have hop : IsOpen ((Ideal.span {d} : Ideal O₀) : Set O₀) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
    have := (isAdic_iff.1 had).1 N
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at this
    rwa [Ideal.span_singleton_eq_span_singleton.2 hN]
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((Ideal.span {d} : Ideal O₀) : Set O₀),
    hop.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ : d ∣ y - x := Ideal.mem_span_singleton.1 hy
  rw [Submodule.Quotient.eq]
  refine ⟨ι c, ?_⟩
  rw [← sub_div, ← map_sub, ← map_sub, hc, map_mul, map_mul]
  simp only [Algebra.linearMap_apply]
  field_simp

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem continuous_of_toLL {X : Type} [TopologicalSpace X] (f : X → O₀)
    (h : Continuous fun x => Bw.toLL (f x)) : Continuous f := by
  have h1 : Continuous fun x => Bw.eO (f x) := continuous_induced_rng.2 h
  simpa [Function.comp_def] using Bw.eO_symm_cont.comp h1

theorem continuous_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (j : Fin m) : Continuous fun g => f g j := by
  apply continuous_of_toLL Bw
  have := ((continuous_apply j).comp hf.1.1).comp Bw.e_cont
  simpa [Function.comp_def] using this

theorem cocycle_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (g h : ↥Gw) (j : Fin m) :
    f (g * h) j = f g j + ∑ b, ((T g : GL (Fin m) O₀) : Matrix (Fin m) (Fin m) O₀) j b * f h b := by
  apply toLL_injective Bw
  have := congrFun (hf.1.2 (Bw.e g) (Bw.e h)) j
  simpa [← map_mul, LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply] using this

end Bridge

section Main

variable (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ)

theorem latT_eq : latT D i s = Gen.Tgl i s := rfl

variable (ψ : GE D →* (D.ntw.Ok i k)ˣ) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i))
  (hψ : ∀ σ ∈ decAt D v, ψ σ = 1)

end Main

end GlobalTheory.BKIntegralToRational
