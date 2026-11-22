import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.LocalRingCardinality.DataKap

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

structure ClsPkg : Type 1 where
  cls : ℕ → Type
  clsFin : ∀ i, Fintype (cls i)
  stab : ∀ i, cls i → Type
  stabGrp : ∀ i c, Group (stab i c)
  stabFin : ∀ i c, Finite (stab i c)
  DGam : ℕ
  DGam_pos : 0 < DGam
  dvd : ∀ i c, Nat.card (stab i c) ∣ DGam

section FormsY

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] (hTau : Fintype.card Tau = R.f)
  {hc : Tau → HCParam R} (C : ColumnChain R Tau hc) [hE : ∀ i, IsEmpty (C.Y i)]
  (A : ColumnsAtT R C) (P : PeriodMap R C)

def formsY : MemberForms LL embLL Pl Tau hc C A P where
  lv := fun i v _ => Fin (R.N i) → A.Fv v
  lv_rank := fun i v _ => Module.finrank_fin_fun (A.Fv v)
  fv := fun i v _ => LinearMap.proj ⟨0, R.N_pos i⟩
  fv_ne := fun i v _ h => one_ne_zero (α := A.Fv v) (LinearMap.congr_fun h 1)
  up := fun _ _ c _ => c
  upT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  lk := fun i v _ => Fin (R.N i) → A.Fv v
  lk_rank := fun i v _ => Module.finrank_fin_fun (A.Fv v)
  te := fun i v _ => Pi.single ⟨0, R.N_pos i⟩ 1
  te_ne := fun i v _ h => by simpa using congrFun h ⟨0, R.N_pos i⟩
  dn := fun _ _ c _ => c
  dnT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil := fun _ _ _ c => c
  dilT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil_one := fun _ _ _ => rfl
  dil_mul := fun _ _ _ _ _ => rfl
  dil_fv := fun i v a _ => ⟨LinearEquiv.smulOfUnit a⁻¹, LinearMap.ext fun x => by
    show x ⟨0, R.N_pos i⟩ = (a : A.Fv v) * (((a⁻¹ : (A.Fv v)ˣ) : A.Fv v) * x ⟨0, R.N_pos i⟩)
    rw [Units.mul_inv_cancel_left]⟩
  dil_stab := fun _ _ _ _ => rfl
  rhoT_dil := fun _ _ _ _ => Subsingleton.elim _ _
  tauOf := fun _ => Fintype.equivOfCardEq (by rw [A.card_vT, hTau])
  seenP := fun _ => true
  lam := fun j τ => lamOf (hc τ) j
  lam_eq := fun j hj τ i => lamOf_eq (hc τ) j hj i
  sg := fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
  Fi := fun _ => ⊥
  Fi_zero := Subsingleton.elim _ _
  ipV := fun _ _ => 0
  lat := fun _ => fmZeroHLat LL
  lat_good := fun _ => fmZeroHLat_good LL
  emb := fun _ => 0
  emb_basis := fun _ => ⟨linearIndependent_empty_type, by
    rw [Set.range_eq_empty, Submodule.span_empty]⟩
  emb_norm := fun i x => by
    rw [fmZeroHLat_maj]
    simp
  rhoT_lat := fun _ _ _ _ => ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩
  Bw := fun _ _ _ => ⊤
  Bw_span := fun _ _ _ => Subsingleton.elim _ _
  clsP := Empty
  stabilizer₂ := fun _ => Unit
  til := fun c => c.elim
  stabMap := fun c => c.elim
  stabMap_inj := fun c => c.elim
  evz_til := fun φ ψ _ => by rw [Subsingleton.elim φ ψ]
  ptC := ⊥
  ipP := 0
  ptLat := fmZeroHLat LL
  ptLat_good := fmZeroHLat_good LL
  ptEmb := 0
  ptEmb_basis := ⟨linearIndependent_empty_type, by rw [Set.range_eq_empty, Submodule.span_empty]⟩
  ptEmb_norm := fun x => by
    rw [fmZeroHLat_maj]
    simp
  beOn := fun _ => 0
  beOn_nonneg := fun _ => le_rfl
  thFree := fun _ _ _ _ => 0
  thFree_nonneg := fun _ _ _ _ => le_rfl

end FormsY

section Member3

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg)

abbrev chain3 : ColumnChain R Tau hc where
  cls := K.cls
  clsFin := K.clsFin
  stab := K.stab
  stabGrp := K.stabGrp
  stabFin := K.stabFin
  DGam := K.DGam
  DGam_pos := K.DGam_pos
  dvd_DGam := fun i _ c => K.dvd i c
  Y := fun _ => Empty
  de := fun _ y => y.elim
  de_ne := fun _ y => y.elim
  rhoDet := fun _ _ => 1
  rhoDet' := fun _ _ => 1
  rho_norm := fun _ _ _ => norm_one
  rho'_norm := fun _ _ _ => norm_one
  unf := fun _ _ _ => 0
  sSharp := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).2.choose else 0
  sSharp_eq := fun i h τ => by rw [dif_pos h]; exact (sInt R (hc τ) ⟨i, h⟩).2.choose_spec.symm
  sDiv := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).1.choose else 0
  sDiv_eq := fun i h τ => by rw [dif_pos h]; exact (sInt R (hc τ) ⟨i, h⟩).1.choose_spec.symm

instance (i : ℕ) : IsEmpty ((chain3 hc K).Y i) := ⟨fun c => Empty.elim c⟩

variable (T : ℕ) [hT : Fact T.Prime]

abbrev classLevelColumnsAt (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) : ColumnsAtT R (chain3 hc K) :=
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  { T := T
    T_prime := hT.out
    vT := Fin R.f
    card_vT := Fintype.card_fin _
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => 1
    Mu0 := ⊥
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => by simp
    duStar := du
    duStar_pos := hdu
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

instance (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) :
    Subsingleton (classLevelColumnsAt hc K T Dst hD du hdu Gam hG).Mram :=
  ⟨fun _ _ => Subtype.ext (funext fun _ => funext fun y => Empty.elim y)⟩

abbrev period3 : PeriodMap R (chain3 hc K) where
  Mt := Z0
  Wz := PUnit
  evz := 0
  Wrow := PUnit
  lowerMap := 0
  period := 0

abbrev mem3 (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam) : Member R Tau hc :=
  ⟨chain3 hc K, classLevelColumnsAt hc K T Dst hD du hdu Gam hG, period3 hc K⟩

end Member3

section Record

variable {R : Ranks} (H : Host R)

variable (hc : Tau2 R → HCParam R) (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * Del)
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ W, 0 < vol W) (K : ClsPkg)
  (T : ℕ) [hT : Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (hwin : (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar ≤ (T : ℝ) ∧
    (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
  (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)

end Record

end Formalism.BasicNotions.Examples₂
