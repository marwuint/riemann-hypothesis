import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.Inhab
open scoped TensorProduct

section SpacesG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem z_anis_gen (n : ℕ) : diagForm (E := E) (n + 1) (fun _ => false) (Pi.single (Fin.last n) 1)
    (Pi.single (Fin.last n) 1) ≠ 0 := by
  rw [diagForm_single_left]
  simp [sgn]

theorem z_orth_gen (n : ℕ) (x : Fin n → E) :
    diagForm (n + 1) (fun _ => false) (extZero n x) (Pi.single (Fin.last n) 1) = 0 := by
  rw [diagForm_single_right, extZero_last]
  simp

theorem vstd_gen (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (diagForm (E := E) n (fun _ => false)) (stdLat n) n := by
  refine ⟨Pi.basisFun E (Fin n), (Pi.basisFun E (Fin n)).linearIndependent,
    (Pi.basisFun E (Fin n)).span_eq, rfl, fun i j => ?_⟩
  rw [Pi.basisFun_apply, Pi.basisFun_apply, diagForm_single]
  simp [sgn]

variable (s : ℕ) (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

def gXr : ℕ → ℕ
  | 0 => 8
  | 1 => (Rt s).rankY 1
  | _ + 2 => 9 + 2 * (2 * s + 15) + 1

theorem gXr_eq (j : ℕ) (hj : j ≤ (Rt s).m) : gXr s j = (Rt s).N j := by
  have : (Rt s).m = 2 := rfl
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  all_goals simp [gXr, Ranks.N, Ranks.rankY, Ranks.r, Rt] <;> omega

def gX (j : ℕ) : HSpace E := posSpace hstar (gXr s j)

def gY : ℕ → HSpace E
  | 0 => lorentzSpace hstar
  | j + 1 => posSpace hstar ((Rt s).rankY (j + 1))

def gIXY : ∀ j, (gX s hstar j).V →ₗ[E] (gY s hstar j).V
  | 0 => extZero 8
  | 1 => LinearMap.id
  | _ + 2 => 0

def spacesG : Spaces (Rt s) F E where
  cm := cm
  T := T
  T_prime := hT
  X := gX s hstar
  X_sig := fun j => posSpace_sigOK hstar (gXr s j)
  X_rank := fun j hj => gXr_eq s j hj
  X_def := fun _ _ _ => Or.inl rfl
  X' := posSpace hstar (9 + 2 * (2 * s + 15))
  X'_sig := posSpace_sigOK hstar _
  X'_rank := rfl
  iX' := extZero (9 + 2 * (2 * s + 15))
  iX'_isom := fun x y => extZero_isom (9 + 2 * (2 * s + 15)) (fun _ => false) (fun _ => false) (fun _ => rfl) x y
  z := Pi.single (Fin.last (9 + 2 * (2 * s + 15))) 1
  z_anis := z_anis_gen _
  z_orth := fun x => z_orth_gen _ x
  Y := gY s hstar
  Y_sig := fun j => match j with
    | 0 => lorentzSpace_signature_ok hstar
    | _ + 1 => posSpace_sigOK hstar _
  Y_rank := fun j _ => match j with
    | 0 => by
      show 8 + 1 = _
      simp [Ranks.rankY, Ranks.r, Rt]
    | _ + 1 => rfl
  iXY := gIXY s hstar
  iXY_isom := fun j hj => match j, hj with
    | 0, _ => fun x y => extZero_isom 8 (fun _ => false) negLast (fun i => negLast_castAdd i) x y
    | 1, _ => fun _ _ => rfl
    | _ + 2, h => absurd h (by have : (Rt s).m = 2 := rfl; omega)
  eYm := LinearEquiv.refl E (Fin (9 + 2 * (2 * s + 15)) → E)
  eYm_isom := fun _ _ => rfl
  zm := Pi.single (Fin.last 8) pz
  zm_norm := lorentz_last_vector_norm T pz hpz
  zm_orth := fun x => lorentz_extension_orthogonal_last pz x
  hypE := fun _ => 0
  hypF := fun _ => 0
  hyp_ee := fun _ _ => by simp
  hyp_ff := fun _ _ => by simp
  hyp_ef := fun i _ => absurd i.isLt (by simp [Ranks.rS, Rt])
  hyp_orthX := fun _ _ => ⟨by simp, by simp⟩
  hyp_orthz := fun _ => ⟨by simp, by simp⟩
  baseSpace_signature_eq := fun _ => by
    show ((8, 1) : ℕ × ℕ) = _
    simp [Ranks.sigY0, Ranks.rS, Rt]
  W := toyW hstar
  W_sig := fun j => match j with
    | 0 => posSpace_sigOK hstar _
    | 1 => lorentzSpace_signature_ok hstar
    | _ + 2 => posSpace_sigOK hstar _
  W_rank := fun j h1 h2 => by
    have : (Rt s).m = 2 := rfl
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · rfl
    · rfl
  W_sigval := fun j h1 h2 τ => by
    have : (Rt s).m = 2 := rfl
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · rfl
    · rfl
  baseSpace_isometric_graded := example_baseSpace_isometric_graded hstar cm hy
  V := fun _ => posSpace hstar (Rt s).nV
  V_sig := fun _ => posSpace_sigOK hstar _
  V_rank := fun _ _ _ => rfl
  Vneg := fun _ => false
  V_std := fun _ _ _ => vstd_gen _

end SpacesG

section RowsG

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)

end RowsG

theorem N_even (R : Ranks) (j : ℕ) : ∃ a : ℕ, R.N j = 2 * a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  exact ⟨a + j * (b + 1), by unfold Ranks.N; rw [ha, hb]; ring⟩

theorem sInt (R : Ranks) (hc : HCParam R) (i : Fin R.m) :
    (∃ a : ℤ, sExp R (hc.e i) (i.1 + 1) = a) ∧ (∃ a : ℤ, sExp' R (hc.e i) (i.1 + 1) = a) := by
  obtain ⟨z, hz⟩ := hc.e_int i
  obtain ⟨a, ha⟩ := N_even R i.1
  obtain ⟨b, hb⟩ := N_even R (i.1 + 1)
  refine ⟨⟨z - a, ?_⟩, ⟨z - b, ?_⟩⟩
  · unfold sExp; rw [Nat.add_sub_cancel, ha, hz]; push_cast; ring
  · unfold sExp'; rw [hb, hz]; push_cast; ring

section MemberG

variable {R : Ranks} (hc : HCParam R) (Tau : Type) [Fintype Tau]

abbrev chainG : ColumnChain R Tau (fun _ => hc) where
  cls := fun _ => Empty
  stab := fun _ c => c.elim
  stabGrp := fun _ c => c.elim
  stabFin := fun _ c => c.elim
  DGam := 1
  DGam_pos := one_pos
  dvd_DGam := fun _ _ c => c.elim
  Y := fun _ => Unit
  de := fun _ _ _ => 1
  de_ne := fun _ _ _ => one_ne_zero
  rhoDet := fun _ c => c.elim
  rhoDet' := fun _ c => c.elim
  rho_norm := fun _ _ c => c.elim
  rho'_norm := fun _ _ c => c.elim
  unf := fun _ c => c.elim
  sSharp := fun i _ => if h : i < R.m then (sInt R hc ⟨i, h⟩).2.choose else 0
  sSharp_eq := fun i h _ => by rw [dif_pos h]; exact (sInt R hc ⟨i, h⟩).2.choose_spec.symm
  sDiv := fun i _ => if h : i < R.m then (sInt R hc ⟨i, h⟩).1.choose else 0
  sDiv_eq := fun i h _ => by rw [dif_pos h]; exact (sInt R hc ⟨i, h⟩).1.choose_spec.symm

instance (i : ℕ) : IsEmpty ((chainG hc Tau).cls i) := ⟨fun c => Empty.elim c⟩

variable (T : ℕ) [hT : Fact T.Prime]

abbrev atTG (Dst : ℝ) (hD : 0 < Dst) (Gam : ℝ) (hG : 1 < Gam) : ColumnsAtT R (chainG hc Tau) :=
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
    duStar := 1
    duStar_pos := one_pos
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

instance (Dst : ℝ) (hD : 0 < Dst) (Gam : ℝ) (hG : 1 < Gam) :
    Subsingleton (atTG hc Tau T Dst hD Gam hG).Mram :=
  ⟨fun _ _ => Subtype.ext (funext fun c => (IsEmpty.false c).elim)⟩

abbrev periodG : PeriodMap R (chainG hc Tau) where
  Mt := Z0
  Wz := PUnit
  evz := 0
  Wrow := PUnit
  lowerMap := 0
  period := 0

end MemberG

def dstarG (Ts Gam : ℝ) : ℝ := (Ts * Gam ^ ((2 : ℝ) / 64)) ^ (64 : ℕ)

theorem dstarG_pos {Ts Gam : ℝ} (hTs : 0 < Ts) (hG : 1 < Gam) : 0 < dstarG Ts Gam := by
  have : 0 < Gam := by linarith
  unfold dstarG; positivity

section Record

abbrev TauG (s : ℕ) : Type := ↥((Rt s).Psi)

variable {s : ℕ}

abbrev memG (hc : HCParam (Rt s)) (T : ℕ) [Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ)
    (hG : 1 < Gam) : Member (Rt s) (TauG s) (fun _ => hc) :=
  ⟨chainG hc (TauG s), atTG hc (TauG s) T (dstarG Ts Gam) (dstarG_pos hTs hG) Gam hG, periodG hc (TauG s)⟩

variable (H : Host (Rt s))

def spG (T : ℕ) [hT : Fact T.Prime] (pz : H.E) (hpz : pz * H.conj pz = (T : H.E)) :
    @Spaces (Rt s) H.F H.E _ _ _ _ H.cmStar _ :=
  letI := H.cmStar
  spacesG s star_isIntegral (cmData H) T hT.out pz
    (by rw [star_eq_conj H pz, mul_comm]; exact hpz)
    (exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x))

variable (hc : HCParam (Rt s))
  (hgap : ∀ (l : ℕ) (h : l + 1 < (Rt s).k - 1), hc.v ⟨l, by omega⟩ - hc.v ⟨l + 1, h⟩ = 4 * 1)
  (hlet : ∀ (l : ℕ) (h : l < (Rt s).k - 2), hc.u ⟨l + 1, by omega⟩ = hc.v ⟨l, by omega⟩ - 1 / 2)

variable (T : ℕ) [hT : Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
  (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / 64) * Ts)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)

end Record

end Formalism.BasicNotions.Examples₂
