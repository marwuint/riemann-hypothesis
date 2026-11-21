import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix

noncomputable section

namespace GlobalTheory.ParamRep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

theorem charpoly_smul_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) :
    (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod := by
  have h := (IsAlgClosed.splits (u • M).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _)
  rw [GlobalTheory.RowTie.EigTwist.roots_charpoly_smul_matrix] at h
  exact h

theorem charpoly_smul_of_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ)
    (L : Multiset ℂ) (h : M.charpoly = (L.map fun α => X - C α).prod) :
    (u • M).charpoly = ((L.map (· * u)).map fun α => X - C α).prod := by
  rw [charpoly_smul_eq_prod, h, roots_multiset_prod_X_sub_C]

theorem prod_Icc_eq_fin {M : Type*} [CommMonoid M] (F : ℕ → M) (t : ℕ) :
    ∏ c ∈ Finset.Icc 1 t, F c = ∏ c : Fin t, F ((c : ℕ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => by rw [add_comm]

theorem charpoly_block {k : Type*} [CommRing k] {r t : ℕ} (M : Matrix (Fin r) (Fin r) k) (d : Fin t → k) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 (Matrix.diagonal d))).charpoly =
      M.charpoly * ∏ c, (X - C (d c)) := by
  rw [Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]
  congr 1
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_diagonal]

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E q) : v ∉ placesOver E p := by
  intro hv'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h1 : (1 : 𝓞 E) ∈ v.asIdeal := by
    have e : (1 : 𝓞 E) = (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv') (v.asIdeal.mul_mem_left _ hv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem locG_tw_tw (hL : Formalism.MainNotions.SumRepresentations.At.TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) :
    A.locG (A.tw (A.tw π A.etaTinv) A.etaT) w = A.locG π w := by
  obtain ⟨h1, h2⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  have d2 := A.locG_dim A.etaT w
  have hu2 := A.etaT_unr w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ hu2).trans d2)
  have hc0 : c ≠ 0 := by
    have := A.frobEig_ne_zero _ hu2
    rw [hc] at this
    simpa [eq_comm] using this
  have hu := A.unr_char _ _ d2 h1 hu2
  have hf : A.frobEig (A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w)) = {1} := by
    rw [A.frobEig_char _ _ c h1 hu2 d2 hc, h2, hc]
    simp [hc0]
  have he : A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w) = A.lpUnr w {1} := by
    rw [A.unr_eq_lpUnr _ hu, hf]
  obtain ⟨-, -, -, e1, e2, -⟩ := hL w (A.locG π w) (A.locG π w) (A.locG A.etaTinv w) (A.locG A.etaT w) 0 d1 d2
  rw [A.locG_tw, A.locG_tw, e1, he, e2]

theorem hecke_split (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    (hB : IsBCV N A i P (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv))
    {w : PlE H} (hw : SplitOut N i w) (hu : A.unr (A.locG (A.tw π A.etaTinv) w))
    {B : ValuationSubring N.Om} {σ : G H.E N.Om} (hBw : IsPlaceOver (F := H.E) B w)
    (hσ : IsFrob (F := H.E) B (normV w) σ) :
    (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) := by
  have e2 : (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := A.pt_loc i P x hP w hw
  have e3 := hB.2.2.2.1 w hw.1
  have s1 := galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)
  have s2 := galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1
    ((1 - (R.nV : ℝ)) / 2)
  have e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
        (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w)) := rfl
  have e5 : ∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) =
      ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
        (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 =
        ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ)) := by ring
    rw [hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]
    have hq := iota_eps N A i hw.2.1 hBw hσ
    have hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) =
        ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq,
        map_units_inv, Units.val_pow_eq_pow_val, map_pow]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]
  rw [e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, e5]
  simp

theorem galPol_twist {w : PlE H} (π : A.CG R.r) (hu : A.unr (A.locG π w)) (u : ℂ)
    (hξ : A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {u}) :
    galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) =
      (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map (· * u)).map fun α => X - C α).prod := by
  obtain ⟨h1, -⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ h1).trans d1)
  rw [A.frobEig_tw _ _ h1, hd, Multiset.map_singleton, Multiset.singleton_inj] at hξ
  unfold galPol
  rw [A.locG_tw, A.frobEig_tw _ _ (A.unr_char _ _ d1 hu h1), A.frobEig_char _ _ d hu h1 d1 hd,
    A.frobEig_tw _ _ hu]
  simp only [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
  simp only [Function.comp]
  rw [← hξ]
  have hq : ((normV w : ℕ) : ℂ) ^ (((1 - (R.nV : ℝ)) / 2 : ℝ) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ (((1 - (R.r : ℝ)) / 2 : ℝ) : ℂ) *
        ((normV w : ℕ) : ℂ) ^ ((-(R.t : ℝ) / 2 : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ (normV_ne_zero w)]
    congr 1
    rw [Ranks.nV]
    push_cast
    ring
  rw [hq]
  congr 2
  ring

theorem map_smul_matrix {k l : Type*} [CommRing k] [CommRing l] {n : Type*} (f : k →+* l) (c : k)
    (M : Matrix n n k) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

section Twist

variable {Γ : Type} [Group Γ]

theorem coe_twGL {k : Type} [CommRing k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((χ g : kˣ) : k) • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  show algebraMap k (Matrix (Fin n) (Fin n) k) ((χ g : kˣ) : k) * _ = _
  rw [← Algebra.smul_def]

theorem twGL_twGL_inv {k : Type} [CommRing k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ⁻¹) χ = ρ := by
  ext g : 2
  rw [coe_twGL, coe_twGL, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]
  simp

theorem mapRep_twGL {k l : Type} [CommRing k] [CommRing l] {n : ℕ} (f : k →+* l) (ρ : Γ →* GL (Fin n) k)
    (χ : Γ →* kˣ) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) =
      Formalism.MainNotions.SumRepresentations.At.twGL (mapRep f ρ) ((Units.map f.toMonoidHom).comp χ) := by
  ext g : 2
  rw [coe_twGL, mapRep_twGL_coe]
  rfl

theorem isSSRep_twGL {k : Type} [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := by
  have key : ∀ W : Submodule k (Fin n → k), IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
    intro W
    refine ⟨fun hW g v hv => ?_, fun hW g v hv => ?_⟩
    · have h1 := hW g v hv
      rw [coe_twGL, Matrix.smul_mulVec] at h1
      exact (W.smul_mem_iff (χ g).ne_zero).1 h1
    · rw [coe_twGL, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW g v hv)
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 h1, h2⟩

end Twist

end GlobalTheory.ParamRep

