import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AmbientLatticeAvoidance
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDecorationExtensionAtPrimes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeInterior
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeInterior
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

noncomputable section

namespace GlobalTheory.KFormsCmp

section Cong

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

def congSub (M : AddSubgroup V) (c : E) : Subgroup (V ≃ₗ[E] V) where
  carrier := {k | (∀ x, k x ∈ M ↔ x ∈ M) ∧ ∀ x ∈ M, c⁻¹ • (k x - x) ∈ M}
  one_mem' := ⟨fun _ => Iff.rfl, fun x _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨fun x => (ha.1 (b x)).trans (hb.1 x), fun x hx => by
    have e : c⁻¹ • ((a * b) x - x) = a (c⁻¹ • (b x - x)) + c⁻¹ • (a x - x) := by
      rw [map_smul, map_sub, ← smul_add]
      congr 1
      show a (b x) - x = _
      abel
    rw [e]
    exact add_mem ((ha.1 _).2 (hb.2 x hx)) (ha.2 x hx)⟩
  inv_mem' := fun {a} ha => ⟨fun x => by
      have := ha.1 (a⁻¹ x)
      rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at this
      exact this.symm, fun x hx => by
      have h1 : a⁻¹ x ∈ M := by
        have := ha.1 (a⁻¹ x)
        rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at this
        exact this.1 hx
      have h2 := ha.2 _ h1
      rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at h2
      have e : c⁻¹ • (a⁻¹ x - x) = -(c⁻¹ • (x - a⁻¹ x)) := by rw [← smul_neg, neg_sub]
      rw [e]
      exact neg_mem h2⟩

end Cong

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem intAt_neg {a : E} (h : IntAt P a) : IntAt P (-a) := by
  have := (IntAt.coe P (-1)).mul h
  simpa using this

end Red

section Primes

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_of_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

theorem g_mem_of_vGs (hP : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    ∃ k, (Pr.g k : 𝓞 X.E) ∈ w.asIdeal := by
  classical
  rcases Finset.mem_union.1 hw with h | h
  · exact ⟨0, hP.g_mem h⟩
  · exact ⟨1, hP.g_mem h⟩

theorem disj (hP : Pr.Ok) (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) (hg : ∀ k, Pr.g k ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hQ : P ∈ QE sel (mu : Chr X.F X.E X.K)) : P ∉ Pr.vGs := fun hw => by
  obtain ⟨k, hk⟩ := g_mem_of_vGs hP hw
  exact notMem_of_QE hs mu hQ (hP.g_prime k) (hg k) hk

theorem pi_notMem (hP : Pr.Ok) (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) (u : Pr.Word) (hT : Pr.T u ∈ S)
    (P : rowSG Pr sel mu) : Pr.piT u ∉ P.1.asIdeal := by
  classical
  intro h
  have hT' : (Pr.T u : 𝓞 X.E) ∈ P.1.asIdeal := by
    rw [← hP.piT_norm u]
    exact Ideal.mul_mem_right _ _ h
  rcases Finset.mem_union.1 P.2 with hw | hw
  · obtain ⟨k, hk⟩ := g_mem_of_vGs hP hw
    have hc : Nat.Coprime (Pr.T u) (Pr.g k) := (Nat.coprime_primes (hP.T_prime u) (hP.g_prime k)).2 (hP.T_ne_g u k)
    have hc' : IsCoprime ((Pr.T u : ℕ) : 𝓞 X.E) ((Pr.g k : ℕ) : 𝓞 X.E) := Nat.Coprime.cast hc
    obtain ⟨a, b, hab⟩ := hc'
    exact one_notMem P.1 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hT') (Ideal.mul_mem_left _ _ hk))
  · exact notMem_of_QE hs mu hw (hP.T_prime u) hT hT'

end Primes

section Top

variable {E : Type} [Field E] {a n : ℕ}

def Ext (a : ℕ) (jx : Sp E n ≃ₗ[E] Sp E n) (j : Sp E (a + 0) ≃ₗ[E] Sp E (a + 0)) : Prop :=
  (∀ x, cpy E n (a + 0) (jx x) = j (cpy E n (a + 0) x)) ∧ ∀ x, atNL E n a (jx x) = atNL E n a x

theorem Ext.one : Ext a (1 : Sp E n ≃ₗ[E] Sp E n) 1 := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Ext.mul {jx jx' : Sp E n ≃ₗ[E] Sp E n} {j j' : Sp E (a + 0) ≃ₗ[E] Sp E (a + 0)} (h : Ext a jx j)
    (h' : Ext a jx' j') : Ext a (jx * jx') (j * j') :=
  ⟨fun x => (h.1 (jx' x)).trans (congrArg j (h'.1 x)), fun x => (h.2 (jx' x)).trans (h'.2 x)⟩

theorem Ext.inv {jx : Sp E n ≃ₗ[E] Sp E n} {j : Sp E (a + 0) ≃ₗ[E] Sp E (a + 0)} (h : Ext a jx j) :
    Ext a jx⁻¹ j⁻¹ := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := h.1 (jx⁻¹ x)
    rw [show jx (jx⁻¹ x) = x from jx.apply_symm_apply x] at this
    rw [this]
    exact (j.symm_apply_apply _).symm
  · have := h.2 (jx⁻¹ x)
    rw [show jx (jx⁻¹ x) = x from jx.apply_symm_apply x] at this
    exact this.symm

end Top

section Levels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

structure Hyp : Prop where
  hX : T.X.Ok
  hP : T.Pr.Ok
  hs : IsSel T.X T.sel
  hg : ∀ k, T.Pr.g k ∈ T.S
  hT : T.Pr.T T.w ∈ T.S
  hL : T.L.Ok T.Ch T.sel T.xi T.cst T.G (D.R.m - 2)
  hTop : T.TopTie

open Classical in

def topM (i : ℕ) (P : T.SB) : AddSubgroup (Sp T.X.E (D.R.N i)) where
  carrier := {y | T.InTopLat i P y}
  zero_mem' := ⟨by rw [map_zero]; exact zero_mem _, by rw [map_zero]; simpa using IntAt.coe P.1 0⟩
  add_mem' := fun hx hy => ⟨by rw [map_add]; exact add_mem hx.1 hy.1, by rw [map_add]; exact hx.2.add hy.2⟩
  neg_mem' := fun hx => ⟨by rw [map_neg]; exact neg_mem hx.1, by rw [map_neg]; exact intAt_neg hx.2⟩

open Classical in

def topK (i : ℕ) (P : T.SB) : Subgroup (T.AutX i) :=
  congSub (topM T i P) (((qOf P.1 : ℕ) : T.X.E) ^ (if P.1 ∈ T.Pr.vGs then 1 else T.depth P))

def LocB (i : ℕ) (b : Option (T.L.β i)) (P : T.SB) (κ : T.AutX i) (v : T.X.K) : Prop :=
  match b with
  | some al => ∃ r : AutY T.X D.R i, (r ∈ Loc.Cbe (Jat (Pr := T.Pr) T.cst.sharp i P.1) (T.L.h i al P) ∧
        ∀ x, r (Loc.inX T.X.E (D.R.N i) (cOf D.R i) x) = Loc.inX T.X.E (D.R.N i) (cOf D.R i) (κ x)) ∧
      v = chiInv T.Ch T.sel T.xi T.cst i P (T.L.h i al P) r
  | none => ∃ (j : T.XP ≃ₗ[T.X.E] T.XP) (jx k : T.AutX i),
      (j ∈ T.Jtop P ∧ (∀ x, jx (cpy T.X.E _ _ x) = cpy T.X.E _ _ (j x)) ∧
        jx (Loc.eN T.X.E (D.R.N i) (D.R.N D.R.m - 1)) = Loc.eN T.X.E (D.R.N i) (D.R.N D.R.m - 1) ∧
        T.InTopCong i P k ∧ κ = jx * k) ∧ v = T.lamM P j

variable {T}

end Levels

section Points

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

abbrev APt (i : ℕ) : Type := AmbientLatticeAvoidance.Pt (R := D.R) T.sel T.xi T.L T.w i

abbrev inG (w : T.Pr.vGs) : T.SB := by classical exact ⟨w.1, Finset.mem_union_left _ w.2⟩

abbrev inQ (P : QE T.sel (T.xi : Chr T.X.F T.X.E T.X.K)) : T.SB := by classical exact ⟨P.1, Finset.mem_union_right _ P.2⟩

structure Over (i : ℕ) (a : APt T i) (p : T.Lab i) : Prop where
  idx : p.1 = a.2.1
  lat : p.2.1.deco.1.N = a.1.deco.1.N
  fT : p.2.1.deco.1.f = a.1.deco.1.f
  frG : ∀ w : T.Pr.vGs, ∀ x ∈ stdAt T.X.E (D.R.N i) w.1, a.1.deco.1.be w (p.2.1.fr (inG T w) x) = redV w.1 x
  frQ : ∀ P, p.2.1.fr (inQ T P) = a.1.fr P
  cos : i + 1 = D.R.m → p.2.2 = a.2.2
  cos' : i + 1 ≠ D.R.m → a.2.2 = ∅ ∧ p.2.2 = Set.univ

variable {T}

end Points

section Moves

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)
  (abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R)))
  (dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ)

variable {T abelian₂ dep}

theorem Hyp.pi (H : Hyp T) (P : T.SB) : T.Pr.piT T.w ∉ P.1.asIdeal := pi_notMem H.hP H.hs T.xi T.w H.hT P

end Moves

end GlobalTheory.KFormsCmp
