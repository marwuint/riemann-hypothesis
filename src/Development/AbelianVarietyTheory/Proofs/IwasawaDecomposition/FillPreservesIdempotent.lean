import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature

noncomputable section

namespace GlobalTheory.RowPar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Filter

theorem exists_ss {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) :
    ∃ r : Γ →* GL (Fin n) k, IsSSRep r ∧ ρ.ker ≤ r.ker ∧
      ∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin n) (Fin n) k).charpoly := by
  obtain ⟨s, hs⟩ := GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf (glRep (QuotientGroup.kerLift ρ))
  let t : (Γ ⧸ ρ.ker) →* GL (Fin n) k :=
    ((LinearMap.toMatrixAlgEquiv' (R := k) (n := Fin n)).toAlgHom.toMonoidHom.comp s).toHomUnits
  have ht : ∀ x, (t x : Matrix (Fin n) (Fin n) k) = LinearMap.toMatrix' (s x) := fun _ => rfl
  have hv : ∀ x v, (t x : Matrix (Fin n) (Fin n) k).mulVec v = s x v := fun x v => by
    rw [ht, LinearMap.toMatrix'_mulVec]
  refine ⟨t.comp (QuotientGroup.mk' _), fun W hW => ?_, fun g hg => ?_, fun g => ?_⟩
  · obtain ⟨W', h1, h2⟩ := hs.1 W fun x v hx => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
      rw [← hv]
      exact hW g v hx
    exact ⟨W', fun g v hx => (hv _ v).symm ▸ h1 (QuotientGroup.mk' _ g) v hx, h2⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg, map_one]
  · have h := GlobalTheory.SemisimplificationCharpoly.charpoly_eq _ _ hs (QuotientGroup.mk' _ g)
    rw [MonoidHom.comp_apply, ht, ← Matrix.charpoly_toLin', Matrix.toLin'_toMatrix', h]
    exact Matrix.charpoly_toLin' _

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}

theorem eq_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    {f f' : G H.E N.Om → Y} (hf : Continuous f) (hf' : Continuous f')
    (h : ∀ᶠ w in cofinite, IsSplitPl H w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → f σ = f' σ) : f = f' := by
  obtain ⟨S, hS, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split H
  refine hC.eq_of_frob (hS.union (eventually_cofinite.1 h)) hf hf' fun v hv hd B hB σ hσ => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  exact hv.2 (hsp v hv.1 hd) B σ hB hσ

variable (A : NAut N)

def redAt (i : N.Loc) {w : what₂.places.Pl} (h : N.w i = w) :
    N.O i →+* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w) :=
  (fbCast (h ▸ N.w_l i) (what₂.places.resChar_prime w) (N.lPrime i).out).symm.toRingHom.comp
    ((A.kFbar i).comp (IsLocalRing.residue (N.O i)))

variable {A}

section Residual

variable (A) (B₀ : what₂.places.Pl → ValuationSubring ℂ)
  (κ : ∀ w, B₀ w →+* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))

variable {A B₀ κ}

end Residual

variable (A)

def FrobFam (i : N.Loc) (f : PlE H → ℂ[X]) : Prop :=
  ∃ F : Qbar (N.l i) → G H.E N.Om → Qbar (N.l i), (∀ z, Continuous (F z)) ∧
    ∀ᶠ w in cofinite, ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ → ∀ z, A.iotaQC i (F z σ) = (f w).eval (A.iotaQC i z)

variable {A}

theorem FrobFam.congr {i : N.Loc} {f f' : PlE H → ℂ[X]} (h : FrobFam A i f) (e : ∀ᶠ w in cofinite, f w = f' w) :
    FrobFam A i f' := by
  obtain ⟨F, h1, h2⟩ := h
  exact ⟨F, h1, (h2.and e).mono fun w hw => hw.2 ▸ hw.1⟩

theorem FrobFam.mul {i : N.Loc} {f f' : PlE H → ℂ[X]} (h : FrobFam A i f) (h' : FrobFam A i f') :
    FrobFam A i fun w => f w * f' w := by
  obtain ⟨F, h1, h2⟩ := h
  obtain ⟨F', h1', h2'⟩ := h'
  refine ⟨fun z σ => F z σ * F' z σ, fun z => (h1 z).mul (h1' z), (h2.and h2').mono fun w hw B σ hB hσ z => ?_⟩
  rw [map_mul, hw.1 B σ hB hσ, hw.2 B σ hB hσ, eval_mul]

open GlobalTheory.RowTie

variable (A) in
theorem twSum_unr (L : List ((Σ a : ℕ, A.CG a) × ℝ)) : ∀ᶠ w in cofinite, ∀ p ∈ L, A.unr (A.locG p.1.2 w) :=
  (eventually_all_finite L.finite_toSet).2 fun p _ => A.locG_unr_ae p.1.2

theorem frobEig_twSum {L : List ((Σ a : ℕ, A.CG a) × ℝ)} {w : PlE H} (h : ∀ p ∈ L, A.unr (A.locG p.1.2 w)) :
    A.unr (twSum N A L w) ∧
      A.frobEig (twSum N A L w) = (L.map fun p => A.frobEig (A.lpTw (A.locG p.1.2 w) p.2)).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons p L ih =>
    have h1 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have h2 := (A.unr_tw _ p.2).2 (h p List.mem_cons_self)
    exact ⟨(A.unr_sum _ _).2 ⟨h2, h1.1⟩, by
      rw [List.map_cons, List.sum_cons, ← h1.2]; exact A.frobEig_sum _ _ h2 h1.1⟩

theorem eq_of_galPol {w : PlE H} {a b : A.LP w} (ha : A.unr a) (hb : A.unr b) {u : ℝ}
    (h : galPol A (A.lpTw a u) = galPol A (A.lpTw b u)) : a = b := by
  have h1 := congrArg Polynomial.roots h
  rw [galPol, galPol, roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h1
  have h2 : A.lpTw a u = A.lpTw b u := by
    rw [A.unr_eq_lpUnr _ ((A.unr_tw a u).2 ha), h1, ← A.unr_eq_lpUnr _ ((A.unr_tw b u).2 hb)]
  simpa only [A.lpTw_add, add_neg_cancel, A.lpTw_zero] using congrArg (A.lpTw · (-u)) h2

variable (A) in

def IsCohSum (n : ℕ) (Sig : List (Formalism.BasicNotions.Part A.CG)) : Prop :=
  (∀ p ∈ Sig, A.csd p.π) ∧ ∀ p ∈ Sig, ∀ τ, (A.infG p.π τ).Nodup ∧
    ∀ z ∈ A.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - (p.d : ℂ)) / 2

section Cusp

open GlobalTheory.CuspRep

variable [IsTotallyComplex H.E]

variable (A) in

def ReadsCusp (e : ∀ a, A.CG a → CG H.E a) : Prop :=
  (∀ a, 1 ≤ a → Function.Injective (e a)) ∧ (∀ a π, 1 ≤ a → (e a π).IsUnitary) ∧
    ∀ a π w, 1 ≤ a → A.unr (A.locG π w) → ∃ B : Multiset ℂˣ, (e a π).HasSat w B ∧
      A.frobEig (A.locG π w) = B.map fun b => ((b⁻¹ : ℂˣ) : ℂ)

theorem hasSat_twist {a : ℕ} {π : CG H.E a} {w : PlE H} {B : Multiset ℂˣ} (h : π.HasSat w B)
    {χ : Formalism.L2.Host.HChar H.E} (hχ : χ.UnrAt w) : (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem isobaricRigid_of_jacquetShalika (hJ : GlobalTheory.Published.JacquetShalikaRigidity) {e : ∀ a, A.CG a → CG H.E a}
    (he : ReadsCusp A e) : IsobaricRigid N A := by
  intro L L' hL hL' h
  let ν := GlobalTheory.HeckeGal.Model.absPow H.E
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow H.E
  let Φ : ℂˣ → ℂ := fun b => ((b⁻¹ : ℂˣ) : ℂ)
  have hΦ : Function.Injective Φ := Units.val_injective.comp inv_injective
  have key : ∀ (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H), (∀ p ∈ L, 1 ≤ p.1.1) →
      (∀ p ∈ L, A.unr (A.locG p.1.2 w)) → ∃ B : Fin L.length → Multiset ℂˣ,
        (∀ j, ((e _ (L.get j).1.2).twist (ν (L.get j).2)).HasSat w (B j)) ∧
          (∑ j, B j).map Φ = A.frobEig (twSum N A L w) := by
    intro L w h1 h2
    choose B hB hB' using fun j : Fin L.length =>
      he.2.2 _ (L.get j).1.2 w (h1 _ (List.get_mem _ _)) (h2 _ (List.get_mem _ _))
    refine ⟨_, fun j => hasSat_twist (hB j) ((hν _).1 w), ?_⟩
    rw [(frobEig_twSum h2).2, ← Multiset.coe_mapAddMonoidHom, map_sum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Eq.trans ?_ (A.frobEig_tw _ (L.get j).2 (h2 _ (List.get_mem _ _))).symm
    rw [hB', Multiset.coe_mapAddMonoidHom, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Φ, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, ν, (hν _).2.1 w,
      Complex.cpow_neg, inv_inv]
    rfl
  obtain ⟨s, hs⟩ := hJ.unitary (fun j : Fin L.length => e _ (L.get j).1.2) (fun j : Fin L'.length => e _ (L'.get j).1.2)
    (fun j => hL _ (List.get_mem _ _)) (fun j => hL' _ (List.get_mem _ _))
    (fun j => he.2.1 _ _ (hL _ (List.get_mem _ _))) (fun j => he.2.1 _ _ (hL' _ (List.get_mem _ _))) ν hν
    (fun j => (L.get j).2) (fun j => (L'.get j).2) (by
      filter_upwards [h, twSum_unr A L, twSum_unr A L'] with w a b b'
      obtain ⟨B, h1, h2⟩ := key L w hL b
      obtain ⟨B', h1', h2'⟩ := key L' w hL' b'
      exact ⟨B, B', h1, h1', Multiset.map_injective hΦ (by rw [h2, h2', a])⟩)
  have inj : ∀ p q : Σ a : ℕ, A.CG a, 1 ≤ p.1 → (⟨p.1, e _ p.2⟩ : Σ a, CG H.E a) = ⟨q.1, e _ q.2⟩ → p = q := by
    rintro ⟨a, π⟩ ⟨b, π'⟩ ha h
    obtain rfl : a = b := (Sigma.mk.inj h).1
    exact congrArg _ (he.1 a ha (eq_of_heq (Sigma.mk.inj h).2))
  have e' : ∀ L : List ((Σ a : ℕ, A.CG a) × ℝ), (L : Multiset _) = Finset.univ.val.map L.get := fun L => by
    rw [Fin.univ_val_map, List.ofFn_get]
  rw [← Multiset.coe_eq_coe, e', e', ← Finset.map_univ_equiv s, Finset.map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun j _ => Prod.ext (inj _ _ (hL _ (List.get_mem _ _)) (hs j).1) (hs j).2

end Cusp

variable (A)

variable {A}

variable (A)

theorem lpDim_twSum (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) :
    A.lpDim (twSum N A L w) = (L.map fun p => p.1.1).sum := by
  induction L with
  | nil => exact A.lpDim_zero w
  | cons p L ih =>
    refine (A.lpDim_sum _ _).trans (congrArg₂ (· + ·) ?_ ih)
    rw [A.lpDim_tw, A.locG_dim]

theorem lpDim_isoLoc (Sig : List (Formalism.BasicNotions.Part A.CG)) (w : PlE H) : A.lpDim (isoLoc N A Sig w) = rankIso N A Sig := by
  induction Sig with
  | nil => exact A.lpDim_zero w
  | cons p L ih =>
    refine (A.lpDim_sum _ _).trans (congrArg₂ (· + ·) ?_ ih)
    rw [GlobalTheory.SpehRigid.spehLoc_eq, lpDim_twSum, GlobalTheory.SpehRigid.flat, List.map_map]
    simp [Function.comp_def, mul_comm]

structure Spec (M : Type) [AddCommGroup M] [Module ℂ M] where

  I : Type

  tp : I → Submodule ℂ M

  loc : I → ∀ w, A.LP w

  sat : I → PlE H → Multiset ℂ

  inf : (H.E →+* ℂ) → Multiset ℂ

namespace Spec

def ofLoc (i : N.Loc) : Spec A (what₂.Mt (N.mu i) (N.j i)) := ⟨A.AV i, A.typeV i, A.locV i, A.satV i, A.infWt i⟩

variable {A} {M : Type} [AddCommGroup M] [Module ℂ M] (S S' : Spec A M)

def IsBC (n : ℕ) (P : S.I) (Pa : List (Formalism.BasicNotions.Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = n ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = S.loc P w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧ A.frobEig (isoLoc N A Pa w) = ubc n (S.sat P w)) ∧
  ∀ τ, isoInf N A Pa τ = S.inf τ

def Sub : Prop := S.inf = S'.inf ∧ ∀ P, ∃ Q, S.tp P = S'.tp Q ∧ S.loc P = S'.loc Q ∧ S.sat P = S'.sat Q

end Spec

variable {A} (S : ∀ μ j, Spec A (what₂.Mt μ j)) (T : ∀ μ, Spec A (what₂.Amb μ)) (c : what₂.Tup → ℕ → A.CG 1)

variable (B₀ : what₂.places.Pl → ValuationSubring ℂ)
  (κ : ∀ w, B₀ w →+* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))

variable {S c}

end GlobalTheory.RowPar

end
