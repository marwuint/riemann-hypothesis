import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCharacterConductorOneExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyColCh
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

noncomputable section

namespace GlobalTheory.LevelUnif

open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil GlobalTheory.SymChain
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)

section Elem

variable {κ : Type} [CommRing κ] {r : ℕ}

def elem {i j : Fin r} (h : i ≠ j) (u : κ) : GL (Fin r) κ :=
  ⟨transvection i j u, transvection i j (-u), by rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j h, neg_add_cancel, transvection_zero]⟩

theorem elem_apply {i j : Fin r} (h : i ≠ j) (u : κ) (a b : Fin r) :
    (elem h u).val a b = (1 : Matrix (Fin r) (Fin r) κ) a b + if i = a ∧ j = b then u else 0 := rfl

theorem edgeSum_one (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) :
    edgeSum Ed (1 : GL (Fin r) κ) = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · exact one_apply_ne fun e => hE a (by rwa [← e] at h)
  · rfl

theorem edgeSum_elem (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) {i j : Fin r} (h : i ≠ j) (hij : Ed i j)
    (u : κ) : edgeSum Ed (elem h u) = u := by
  have h1 : ∀ a b, (if Ed a b then (elem h u).val a b else 0) = if i = a then (if j = b then u else 0) else 0 := fun a b => by
    rw [elem_apply]
    by_cases h2 : Ed a b
    · rw [if_pos h2, one_apply_ne fun e => hE a (by rwa [← e] at h2), zero_add, ite_and]
    · rw [if_neg h2, ← ite_and, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h2 hij
  unfold edgeSum
  simp only [h1]
  simp

theorem elem_mem_unipCol {i j : Fin r} (h : i ≠ j) (hij : i.val < j.val) (u : κ) (a c : ℕ) (hc : j.val ≠ c) :
    elem h u ∈ unipCol κ r a c := by
  refine ⟨⟨fun x y hxy => ?_, fun x => ?_⟩, fun x y h1 h2 h3 => ?_⟩
  · have hxy' : y.val < x.val := hxy
    rw [elem_apply, one_apply_ne (fun e => by rw [e] at hxy'; omega), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    omega
  · rw [elem_apply, one_apply_eq, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact h rfl
  · rw [elem_apply, one_apply_ne (fun e => by rw [e] at h2; omega), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    omega

end Elem

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
  {PP : Pl D.host.E} (h : IsIdemAt q.e PP) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
include hψ in
theorem chr_near {t : kˣ} (ht : IsUnif t) {y y' : k} (hy : valuation k (y - y') < 1) :
    ψ (((t⁻¹ : kˣ) : k) * y) = ψ (((t⁻¹ : kˣ) : k) * y') := by
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  have triv : ψ (((t⁻¹ : kˣ) : k) * (y - y')) = 1 := (hψ 1).2 (by simp) _ (by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, map_one, inv_mul_le_one₀ tp]
    exact (ht _).1 hy)
  rw [show ((t⁻¹ : kˣ) : k) * y = ((t⁻¹ : kˣ) : k) * (y - y') + ((t⁻¹ : kˣ) : k) * y' by ring, AddChar.map_add_eq_mul, triv, one_mul]

include h hψ in

theorem exists_res {t : kˣ} (ht : IsUnif t) : ∃ α : AddChar (kP PP) ℂ,
    ∀ z, (ψ (((t⁻¹ : kˣ) : k) * prO q z) : ℂ) = α (Ideal.Quotient.mk _ z) := by
  have wd : ∀ z z' : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = Ideal.Quotient.mk PP.asIdeal z' →
      ψ (((t⁻¹ : kˣ) : k) * prO q z) = ψ (((t⁻¹ : kˣ) : k) * prO q z') := fun z z' e =>
    chr_near hψ ht (by rw [← map_sub, ← prO_lt q h]; exact Ideal.Quotient.eq.1 e)
  choose l hl using Ideal.Quotient.mk_surjective (I := PP.asIdeal)
  refine ⟨{ toFun := fun u => ψ (((t⁻¹ : kˣ) : k) * prO q (l u))
            map_zero_eq_one' := by rw [wd _ 0 (by rw [hl, map_zero])]; simp
            map_add_eq_mul' := fun a b => by
              rw [wd _ (l a + l b) (by rw [map_add, hl, hl, hl]), map_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul] },
    fun z => congrArg (fun c : Circle => (c : ℂ)) (wd _ z (hl _)).symm⟩

include h in

theorem exists_near {y : k} (hy : valuation k y ≤ 1) : ∃ z, valuation k (y - prO q z) < 1 := by
  obtain ⟨-, hi, hd⟩ := place_facts q h
  have h2 : {x : k | valuation k (x - y) < 1} ∈ nhds y := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds h2
  have ha' : valuation k ((ofSplit q).pr a - y) < 1 := ha
  have ha1 : valuation k ((ofSplit q).pr a) ≤ 1 := by
    simpa using Valuation.map_add_le (valuation k) ha'.le hy
  obtain ⟨r, s, hs, e⟩ := (hi a).1 ((Valuation.mem_integer_iff _ _).2 ha1)
  have e' : prO q s * (ofSplit q).pr a = prO q r :=
    ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
  obtain ⟨t, p, hp, htp⟩ := PP.isMaximal.exists_inv hs
  refine ⟨t * r, ?_⟩
  have e2 : prO q t * prO q s + prO q p = 1 := by rw [← map_mul, ← map_add, htp, map_one]
  have e3 : y - prO q (t * r) = (ofSplit q).pr a * prO q p - ((ofSplit q).pr a - y) := by
    rw [map_mul, ← e']
    linear_combination (-(ofSplit q).pr a) * e2
  rw [e3]
  refine Valuation.map_sub_lt _ ?_ ha'
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ha1) ((prO_lt q h p).1 hp)

include h hψ in

theorem near_of_res {t t' : kˣ} (ht : IsUnif t) (ht' : IsUnif t')
    (he : ∀ z, ψ (((t⁻¹ : kˣ) : k) * prO q z) = ψ (((t'⁻¹ : kˣ) : k) * prO q z)) :
    valuation k ((t : k) - t') < valuation k (t : k) := by
  have h1 : ∀ y, valuation k y ≤ 1 → ψ (((t⁻¹ : kˣ) : k) * y) = ψ (((t'⁻¹ : kˣ) : k) * y) := fun y hy => by
    obtain ⟨z, hz⟩ := exists_near q h hy
    rw [chr_near hψ ht hz, chr_near hψ ht' hz, he]
  set c : k := ((t⁻¹ : kˣ) : k) - ((t'⁻¹ : kˣ) : k) with hc
  have h2 : valuation k c ≤ 1 := by
    by_cases c0 : c = 0
    · rw [c0, map_zero]; exact zero_le
    have cp : 0 < valuation k c := zero_lt_iff.2 ((map_ne_zero _).2 c0)
    have := (hψ c).1 fun y hy => by
      have h3 := h1 (c⁻¹ * y) (by rw [map_mul, map_inv₀, inv_mul_le_one₀ cp]; exact hy)
      rw [← mul_inv_eq_one, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, ← hc,
        mul_inv_cancel_left₀ c0] at h3
      exact h3
    simpa using this
  have e : (t : k) - t' = (t : k) * (-c * t') := by
    rw [hc, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    field_simp
    ring
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  rw [e, map_mul]
  refine mul_lt_of_lt_one_right tp ?_
  rw [map_mul, Valuation.map_neg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h2) ((ht' _).2 le_rfl)

theorem psiAt_eq {Ψ : AddChar (AF D.host.F) ℂ} (hc : (ofSplit q).IsChar Ψ ψ) (y : D.host.E) :
    Formalism.IndefR.Mi.psiAt Ψ q.e y = ψ ((ofSplit q).pr y) := by
  rw [hc]
  change _ = Ψ (Algebra.trace _ _ (incA D D.host.xi0 * q.sec (q.pr (incA D y))))
  rw [q.sec_pr, Formalism.IndefR.Mi.psiAt, map_mul (incA D), mul_left_comm]

end Local

theorem norm_notMem_sq {D : D7} {PP : Pl D.host.E} (h : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by
  have hspl : ∀ k, Formalism.MainNotions.S.SplitsCompl D.host.E (D.host.g k) := by
    intro k
    have hp := D.host.g_prime k
    have := Formalism.MainNotions.BridgeLemma.span_isMaximal hp
    apply Formalism.MainNotions.S.splitsCompl_of_ncard _ _ hp
    rw [← IsDedekindDomain.coe_primesOverFinset (Formalism.MainNotions.BridgeLemma.span_ne_bot hp) (𝓞 D.host.E), ← Formalism.MainNotions.BridgeLemma.image_plOver _ hp,
      (Formalism.MainNotions.BridgeLemma.injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k
  rw [Nat.cast_mul] at h
  obtain ⟨k, hk⟩ : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal :=
    (PP.isPrime.mem_or_mem h).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
  obtain ⟨h1, h2⟩ := hspl k _ PP.isMaximal hk
  unfold Formalism.L2.Col.qOf
  rw [h1]
  exact h2

section Levels

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}

theorem chi_of_eq {P P' : LevelP Pg r ℂ} (e : P = P') (x : G0 Pg r) (h : x ∈ P'.H) :
    ∃ h' : x ∈ P.H, P.chi ⟨x, h'⟩ = P'.chi ⟨x, h⟩ := by
  subst e
  exact ⟨h, rfl⟩

theorem prod_single {ι : Type} [Fintype ι] (pl : ι ≃ Pg) (α : ∀ i, AddChar (kP (pl i).1) ℂ) (Ed : Fin r → Fin r → Prop)
    [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) {i j : Fin r} (h : i ≠ j) (hij : Ed i j) (n : ι) (u : kP (pl n).1) :
    ∏ m, α m (edgeSum Ed ((Pi.mulSingle (pl n) (elem h u) : G0 Pg r) (pl m))) = α n u := by
  rw [Finset.prod_eq_single n, Pi.mulSingle_eq_same, edgeSum_elem Ed hE h hij]
  · intro m _ hm
    rw [Pi.mulSingle_eq_of_ne (pl.injective.ne hm), edgeSum_one Ed hE, AddChar.map_zero_eq_one]
  · intro hn
    exact absurd (Finset.mem_univ n) hn

theorem single_mem (H : ∀ PP : Pg, Subgroup (GL (Fin r) (kP PP.1))) (n : Pg) {x : GL (Fin r) (kP n.1)} (hx : x ∈ H n) :
    (Pi.mulSingle n x : G0 Pg r) ∈ Subgroup.pi Set.univ H := fun PP _ => by
  by_cases e : PP = n
  · subst e
    rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne e]
    exact (H PP).one_mem

end Levels

theorem edgeSum_eq_supSum {κ : Type} [CommRing κ] {r : ℕ} (g : GL (Fin r) κ) :
    edgeSum supEdge g = Formalism.IndefR.Mi.supSum (g : Matrix (Fin r) (Fin r) κ) := by
  unfold edgeSum Formalism.IndefR.Mi.supSum
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
    · exact if_pos (show supEdge i ⟨i.1 + 1, h⟩ from rfl)
    · intro j _ hj
      exact if_neg (fun hj' => hj (Fin.ext hj'))
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · refine Finset.sum_eq_zero fun j _ => ?_
    refine if_neg (fun hj => ?_)
    have := j.2
    unfold supEdge at hj
    omega

end GlobalTheory.LevelUnif

end
