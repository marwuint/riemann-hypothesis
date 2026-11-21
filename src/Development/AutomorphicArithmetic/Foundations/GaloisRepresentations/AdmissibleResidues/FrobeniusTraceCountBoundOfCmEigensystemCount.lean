import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.FrobeniusTraceCountBoundOfRatEigensystemCount
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CountSys
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.KlevThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.EventuallyNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatK
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IntK
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.KlevThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.EventuallyNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SignNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FrobEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntEqProdOfGaloisPermutedIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdicNormProdLeProdOfInjectiveClasses
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MapTraceEqSumRootsOfCharpolyMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowResDegPlaceNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockConjugateRankThreeRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicCharacterRestrictCmFieldEqCyclotomicPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LevelTwistCyclotomicPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsIrrTwistAndRepIsoOfTwistRepIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleRankThreeStrengthen

noncomputable section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

namespace UpperTheory.GalN.V.Win.N

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

def CountK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → (∀ i, m i + m i.rev = 1 - n) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m (1 - n), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmKN ι M m)

def CountP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmPN ι M m)

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Af in
theorem countP :
    UpperTheory.V.Af.Hypotheses₂ → LevelPN → CountP := by
  intro hP hL K _ _ _ hK n hn
  classical
  obtain ⟨c, A, hcard⟩ := cardP hP K n hn
  refine ⟨c, A, fun m wt hm hwt H hH M hM p w hp hw hpM hpd => ?_⟩
  have hwM : (M : 𝓞 K) ∉ w.asIdeal := natCast_notMem_of_not_dvd hp hw hpM
  let Wd := {v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}
  let sys : CuspSub K n → Wd → Multiset ℂ := fun π v =>
    if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0
  have hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B := by
    intro π v B hB
    have h : ∃ B, (CG.mk π).HasSat v.1 B := ⟨B, hB⟩
    simp only [sys, dif_pos h]
    rw [h.choose_spec.unique hB]
  have hsat : ∀ π ∈ SigP K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B := fun π hπ v =>
    satK hP K n M π hπ.2.2 v.1 v.2
  obtain ⟨D, hD, cl, hcl, hβ⟩ := exists_eigData (SigP K m M) (fun π π' => π.Iso π') sys
    (fun π hπ π' _ h => funext fun v => by
      obtain ⟨B, hB⟩ := hsat π hπ v
      rw [hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])
    (c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)
    (fun σ π hπ => by
      obtain ⟨π', hπ', h⟩ := conjPrime₂ hP K hK n hn m hm M hM σ π hπ
      refine ⟨π', hπ', fun v => ?_⟩
      obtain ⟨B, hB⟩ := hsat π hπ v
      obtain ⟨B', hB', e⟩ := h v.1 B hB
      rw [hsys π v B hB, hsys π' v B' hB', e])
    ⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := wt)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]
      simp)
    (by exact zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact win_algSat (by omega) π m _ hwt hπ.1 hB)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact intP hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)
  refine ⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩
  have hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // AdmPN ι M m r}, ∃ π : ↥(SigP K m M), IsSSRep r.1 ∧
      ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v) := by
    intro r
    obtain ⟨π, h1, h2, h3⟩ := r.2.aut
    obtain ⟨hπ, hF⟩ := hL K hK n hn m hm M hM l hl2 Ω ι r.1 π r.2.level r.2.safe r.2.unl h1 h2 h3
    refine ⟨⟨π, hπ⟩, h3.1, fun v hv => ?_⟩
    obtain ⟨B, hB⟩ := hsat π hπ v
    rw [hsys π v B hB]
    exact hF v.1 hv B hB
  choose f hss hf using hform
  refine ⟨fun r => cl (f r), fun r r' h => ?_, fun r => ?_⟩
  · refine isoOfFrob hP K Ω l ι n r.1 r'.1 r.2.level.cont r'.2.level.cont (hss r) (hss r') ?_
    filter_upwards [eventually_natCast_notMem (F := K) (M := M) (by omega),
      eventually_natCast_notMem (F := K) hl.out.ne_zero] with v hvM hvl
    refine ⟨sys (f r) ⟨v, hvM⟩, hf r ⟨v, hvM⟩ hvl, ?_⟩
    rw [hcl _ _ h]
    exact hf r' ⟨v, hvM⟩ hvl
  · rw [hβ]
    refine hf r ⟨w, hwM⟩ (natCast_notMem_of_not_dvd hp hw fun h => hlp ?_)
    exact ((Nat.prime_dvd_prime_iff_eq hp hl.out).1 h).symm

end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
  UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Br

private theorem bit_of_fibre {X U : Type} (R : X → X → Prop) (hs : ∀ x y, R x y → R y x)
    (ht : ∀ x y z, R x y → R y z → R x z) (Q : X → U → Prop) (hQ : ∀ x, ∃ u, Q x u)
    (h2 : ∀ u x₀ x x', Q x₀ u → Q x u → Q x' u → ¬ R x₀ x → ¬ R x₀ x' → R x x') :
    ∃ g : X → U × Bool, (∀ x x', g x = g x' → R x x') ∧ ∀ x, Q x (g x).1 := by
  classical
  choose u hu using hQ
  have hex : ∀ x : X, ∃ y, Q y (u x) := fun x => ⟨x, hu x⟩
  refine ⟨fun x => (u x, decide (R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x)), fun x x' h => ?_, hu⟩
  obtain ⟨h1, h3⟩ := Prod.ext_iff.1 h
  simp only at h1 h3
  have h0 := Classical.epsilon_spec (hex x)
  rw [← h1, decide_eq_decide] at h3
  have hx' : Q x' (u x) := h1 ▸ hu x'
  by_cases hc : R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x
  · exact ht _ _ _ (hs _ _ hc) (h3.1 hc)
  · exact h2 _ _ _ _ h0 (hu x) hx' hc fun h4 => hc (h3.2 h4)

private theorem iso_symm {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') :
    RepIso r' r := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, fun s => by rw [hg s]; group⟩

private theorem iso_trans {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' r'' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (h' : RepIso r' r'') : RepIso r r'' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g' * g, fun s => by rw [hg' s, hg s]; group⟩

private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  obtain ⟨h, h1, h2, h3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank ℚ p w hp hw
  rw [Module.finrank_self] at h2
  rw [h3, le_antisymm h2 h1, pow_one]

private theorem exists_over (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (f : ℕ), v.under (𝓞 ℚ) = w ∧ (p : 𝓞 K) ∈ v.asIdeal ∧ 1 ≤ f ∧ f ≤ 2 ∧ normV v = p ^ f := by
  haveI := w.isMaximal
  obtain ⟨Q, hQ, hL⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) w.asIdeal
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : (p : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := hL.over ▸ hw
    simpa [Ideal.under, Ideal.mem_comap] using this
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hpQ)
  obtain ⟨f, f1, f2, f3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank K p ⟨Q, hQ.isPrime, h0⟩ hp hpQ
  exact ⟨⟨Q, hQ.isPrime, h0⟩, f, HeightOneSpectrum.ext hL.over.symm, hpQ, f1, h2 ▸ f2, f3⟩

private theorem not_mem_of_coprime {F : Type} [Field F] [NumberField F] {p a : ℕ} (h : p.Coprime a)
    (w : HeightOneSpectrum (𝓞 F)) (hw : (p : 𝓞 F) ∈ w.asIdeal) : (a : 𝓞 F) ∉ w.asIdeal := fun ha => by
  obtain ⟨x, y, e⟩ : IsCoprime (p : 𝓞 F) (a : 𝓞 F) := Nat.Coprime.cast h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw)
    (w.asIdeal.mul_mem_left _ ha)))

private theorem exists_avoid {N : ℕ} (d : Fin (N + 1) → ℤ) (hd : ∀ i j, i ≠ j → IsCoprime (d i) (d j)) {p : ℕ} (hp : p.Prime) :
    ∃ u : Fin N → Fin (N + 1), Function.Injective u ∧ ∀ i, ¬ (p : ℤ) ∣ d (u i) := by
  by_cases h : ∃ j, (p : ℤ) ∣ d j
  · obtain ⟨j, hj⟩ := h
    refine ⟨j.succAbove, Fin.succAbove_right_injective, fun i hi => ?_⟩
    have := (hd _ _ (Fin.succAbove_ne j i)).isUnit_of_dvd' hi hj
    exact (Nat.prime_iff_prime_int.1 hp).not_unit this
  · exact ⟨Fin.succ, Fin.succ_injective _, fun i hi => h ⟨_, hi⟩⟩

private theorem map_inv_inv (B : Multiset ℂ) : (B.map (·⁻¹)).map (·⁻¹) = B := by
  rw [Multiset.map_map]
  simp

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem trace_conj_gl3 {k : Type} [Field k] (g x : GL (Fin 3) k) :
    ((g * x * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).trace = (x : Matrix (Fin 3) (Fin 3) k).trace := by
  rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem place_over_rational_prime (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (hw : (p : 𝓞 K) ∈ w.asIdeal) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨w.under (𝓞 ℚ), ?_⟩
  change (p : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  rw [Ideal.mem_comap, map_natCast]
  exact hw

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem not_mem_of_distinct_prime {K : Type} [Field K] [NumberField K] {p l : ℕ} (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime)
    (hl : l.Prime) (hlp : l ≠ p) (hw : (p : 𝓞 K) ∈ w.asIdeal) : (l : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hc : IsCoprime (l : 𝓞 K) (p : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hl hp).2 hlp)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h) (w.asIdeal.mul_mem_left b hw)))

private theorem admissible_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (h : Adm3N ι e N ρ) :
    AdmKN ι N ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (tw ρ (cycBar K Ω l)⁻¹) := by
  refine ⟨(UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 ρ h.irr, h.aut, ?_, Keep.oddTw _ h.unl⟩
  have h1 := UpperTheory.level_twist_cyclotomic_pow K Ω l 3 N _ ρ (-1) h.level
  rw [zpow_neg_one] at h1
  convert h1 using 1
  funext i
  fin_cases i <;> simp <;> ring

end

end UpperTheory.GalN.V.Win.N
