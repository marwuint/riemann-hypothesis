import Formalism.LocalRingCardinality.SpanPowerMembership.TwistRecordRowDimensionZero

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

section Rows5

variable {R : Ranks} (W : Type) (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)

end Rows5

section Record

variable {R : Ranks} (H : Host R)

theorem pz_ne {T : ℕ} [hT : Fact T.Prime] {z : H.E} (h : z * H.conj z = (T : H.E)) : z ≠ 0 := by
  rintro rfl
  exact hT.out.ne_zero (by exact_mod_cast (zero_mul _).symm.trans h |>.symm)

theorem norm_quotient_mul_conj {T T' : ℕ} [Fact T'.Prime] {z z' : H.E} (h : z * H.conj z = (T : H.E))
    (h' : z' * H.conj z' = (T' : H.E)) : z / z' * H.conj (z / z') * (T' : H.E) = (T : H.E) := by
  have h1 := pz_ne H h'
  have h2 : H.conj z' ≠ 0 := (map_ne_zero H.conj).mpr h1
  rw [map_div₀, ← h, ← h']
  field_simp

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

abbrev sData5 (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) :
    Formalism.MainNotions.S.Draft.SData R H.F H.E (conjF H) W (Tau2 R) hcW where
  cdScale := cdS
  cdScale_pos := hcdS
  Del := Del
  Del_pos := hDel
  cloud_gap := hgap
  letter := lt
  letter_inj := hlt
  u_letter := hlet
  HH := EuclideanSpace ℂ (Fin 0)
  Cu := fun _ => EuclideanSpace ℂ (Fin 0)
  Pu := fun _ => 0
  volN := fun _ => 1
  volH := fun _ => 1
  volN_pos := fun _ => one_pos
  volH_pos := fun _ => one_pos
  Term := fun _ _ => Empty
  aTerm := fun _ _ t => t.elim
  isId := fun _ => False
  inS := fun _ => False
  relevant := fun _ => False
  FeqF := fun _ => False
  Gterm := fun t => t.elim
  atP := locAdj (conjF H) {H.g 0, H.g 1} (slocH H) (fun p hp => (splH H hg ht.jac p hp).some)
  PlF := HeightOneSpectrum (𝓞 H.F)
  BBne := fun _ _ => False
  generic := fun _ => False
  Pair := fun _ _ => Empty
  pfst := fun t => t.elim
  psnd := fun t => t.elim
  s0 := fun _ => 0
  scalarPair := fun _ => False
  pval := fun _ => 0
  ptOf := fun t => t.elim
  cTerm := fun _ => 0
  massPair := fun _ => 0
  meanCount := fun _ _ _ => 0

abbrev memW (K : W → ClsPkg) (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ)
    (hdu : ∀ u, 0 < du u) (Gam : ℝ) (hG : 1 < Gam) (u : W) : Member R (Tau2 R) (hcW u) :=
  mem3 (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

end Record

end Formalism.BasicNotions.Examples₂
