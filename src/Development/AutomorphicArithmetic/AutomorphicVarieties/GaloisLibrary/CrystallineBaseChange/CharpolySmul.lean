import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.JumpsOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open scoped Matrix

open private UpperTheory.V.Af.infOf_of_weights UpperTheory.V.Af.exists_over from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
open private UpperTheory.V.Af.NewformAutomorphy.ev_not_mem UpperTheory.V.Af.NewformAutomorphy.scale_charpoly
  UpperTheory.V.Af.NewformAutomorphy.ss_of_tw from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere

open UpperTheory.V UpperTheory.V.Af

private theorem flag_stable {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (D N N' : Subgroup Γ) (hN : N ≤ N')
    (hc : ∀ d ∈ D, ∀ s ∈ N, d⁻¹ * s * d ∈ N) (χ : Fin 2 → Γ →* kˣ) (hne : ∃ s ∈ N, χ 0 s ≠ χ 1 s)
    (h : IsFlagOn r N' fun i => (χ i).comp N'.subtype) :
    ∃ κ, IsFlagOn r D κ ∧ ∀ i (s : ↥D), (s : Γ) ∈ N → κ i s = χ i s := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨s0, hs0, hne⟩ := hne
  let M : Γ →* GL (Fin 2) k := (MulAut.conj g).toMonoidHom.comp r
  have hM : ∀ s, M s = g * r s * g⁻¹ := fun _ => rfl
  have h1 : ∀ s ∈ N, M s 1 0 = 0 := fun s hs => (hg ⟨s, hN hs⟩).1 1 0 (by decide)
  have h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s := fun s hs i => (hg ⟨s, hN hs⟩).2 i
  have hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j := fun s t i j => by
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ∀ d ∈ D, M d 1 0 = 0 := fun d hd => by
    have e : s0 * d = d * (d⁻¹ * s0 * d) := by group
    have e2 := hmul s0 d 1 0
    have e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0 := by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
    rw [e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3] at e2
    have : (χ 0 s0 : k) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
    apply mul_left_cancel₀ this
    linear_combination e2
  refine ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => M s i i
      map_one' := by simp
      map_mul' := fun s t => by
        rw [Subgroup.coe_mul, hmul]
        fin_cases i
        · simp [h3 _ t.2]
        · simp [h3 _ s.2] }, ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact h3 _ s.2
  · exact absurd hij (by decide)

private theorem dual_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem ss_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  refine UpperTheory.V.Af.NewformAutomorphy.ss_of_tw _ χ⁻¹ ?_
  convert h
  ext s : 2
  rw [tw_val, tw_val, smul_smul]
  simp

private theorem place_of {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} [hp : Fact p.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp.out)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

private theorem cont_cycBar (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

private theorem cyc_inf {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun k hk h => ?_⟩
  have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [he, hu.unit_spec, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  omega

private theorem charpoly_smul {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have := UpperTheory.V.Af.NewformAutomorphy.scale_charpoly φ (c • M) c⁻¹ (inv_ne_zero hc) (B.map (φ c * ·)) (by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, h, Multiset.map_map]
    simp only [Function.comp_def, map_inv₀, inv_mul_cancel_left₀ hc'])
  rwa [Multiset.map_map] at this

end UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere

