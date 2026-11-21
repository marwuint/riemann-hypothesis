import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistedTriples
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormSpanRepNondegenerateMapRepIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingsConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicAutomorphismUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompareIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SameCharacterCommonExtension

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TwistedSelmerCompare

theorem isSSRep_map_iff {Γ K L : Type} [Group Γ] [Field K] [Field L] [CharZero K] [CharZero L] (f : K →+* L)
    {a : ℕ} (ρ : Γ →* GL (Fin a) K) : IsSSRep (mapRep f ρ) ↔ IsSSRep ρ :=
  ⟨fun h => _root_.GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate Γ K a ρ ((_root_.GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff Γ K L f a ρ).1 (_root_.GlobalTheory.isSSRep_trace_nondegenerate Γ L a _ h)),
    fun h => _root_.GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate Γ L a _ ((_root_.GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff Γ K L f a ρ).2 (_root_.GlobalTheory.isSSRep_trace_nondegenerate Γ K a ρ h))⟩

section Param

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem speh_twist (p : Part A.CG) (χ : A.CG 1) (w : PlE H) (c : ℂ) (hp : A.unr (A.locG p.π w))
    (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (spehLoc N A p w) ∧ A.unr (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) ∧
      A.frobEig (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) = (A.frobEig (spehLoc N A p w)).map (· * c) := by
  have hd := A.locG_dim χ w
  have hp' : A.unr (A.locG (A.tw p.π χ) w) := by rw [A.locG_tw]; exact A.unr_char _ _ hd hp hχ
  have he : A.frobEig (A.locG (A.tw p.π χ) w) = (A.frobEig (A.locG p.π w)).map (· * c) := by
    rw [A.locG_tw]; exact A.frobEig_char _ _ c hp hχ hd hc
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp, i1⟩, (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp', i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp') i2, A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp) i1, i3,
      A.frobEig_tw _ _ hp, A.frobEig_tw _ _ hp', he, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 2
    funext x
    simp only [Function.comp_apply]
    ring

theorem iso_twist (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) (c : ℂ)
    (hS : ∀ p ∈ S, A.unr (A.locG p.π w)) (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (isoLoc N A S w) ∧ A.unr (isoLoc N A (twistIso N A S χ) w) ∧
      A.frobEig (isoLoc N A (twistIso N A S χ) w) = (A.frobEig (isoLoc N A S w)).map (· * c) := by
  induction S with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [isoLoc, twistIso, A.frobEig_zero]⟩
  | cons p S ih =>
    obtain ⟨i1, i2, i3⟩ := ih fun q hq => hS q (List.mem_cons_of_mem _ hq)
    obtain ⟨j1, j2, j3⟩ := speh_twist N A p χ w c (hS p List.mem_cons_self) hχ hc
    change A.unr (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) ∧
      A.unr (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) ∧
      A.frobEig (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) =
        (A.frobEig (A.lpSum (spehLoc N A p w) (isoLoc N A S w))).map (· * c)
    refine ⟨(A.unr_sum _ _).2 ⟨j1, i1⟩, (A.unr_sum _ _).2 ⟨j2, i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ j2 i2, A.frobEig_sum _ _ j1 i1, i3, j3, Multiset.map_add]

theorem galPol_twist (S : List (Part A.CG)) (t : ℝ) : ∀ᶠ w in Filter.cofinite,
    galPol A (A.lpTw (A.lpChar (isoLoc N A S w) (A.locG A.etaTinv w)) t) =
      galPol A (A.lpTw (isoLoc N A (twistIso N A S A.etaTinv) w) t) := by
  have h : ∀ᶠ w in Filter.cofinite, ∀ p ∈ {p | p ∈ S}, A.unr (A.locG p.π w) :=
    (Filter.eventually_all_finite (List.finite_toSet S)).2 fun p _ => A.locG_unr_ae p.π
  filter_upwards [h] with w hw
  have hχ := (A.etaTinv_def w).1
  have hd := A.locG_dim A.etaTinv w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 ((A.frobEig_card _ hχ).trans hd)
  obtain ⟨i1, i2, i3⟩ := iso_twist N A S _ w c hw hχ hc
  unfold galPol
  rw [A.frobEig_tw _ _ i2, A.frobEig_tw _ _ (A.unr_char _ _ hd i1 hχ), i3, A.frobEig_char _ _ c i1 hχ hd hc]

theorem splitOut_ae (a : N.Loc) : ∀ᶠ w in Filter.cofinite, (SplitOut N a w ↔ IsSplitPl H w) := by
  have h1 : (placesOver H.E (N.l a)).Finite := by
    have h0 : Ideal.span {((N.l a : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (N.lPrime a).out.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    simpa [Ideal.dvd_span_singleton, placesOver] using hv
  filter_upwards [h1.compl_mem_cofinite, (N.S a).eventually_cofinite_notMem,
    (N.Q a).eventually_cofinite_notMem] with w a1 a2 a3
  exact ⟨fun h => h.1, fun h => ⟨h, a1, a2, a3⟩⟩

end Param

variable (D : D7)

theorem triple_iff (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG))
    (h : HasParamW D.nd D.naut a σ Sg) (s : TwistedTriples.Trip D a) : TwistedTriples.IsTripleOf D a σ s ↔ IsTriple D a s Sg := by
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    rw [← isSSRep_map_iff (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a))]
    have : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    rw [this]
  · refine Filter.eventually_congr ?_
    filter_upwards [galPol_twist D.nd D.naut Sg ((1 - (D.R.nV : ℝ)) / 2), splitOut_ae D.nd a] with w h1 h2
    rw [h2]
    refine forall_congr' fun hw => forall_congr' fun B => forall_congr' fun g => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [← h1, h.2.2 w hw, ← Polynomial.map_map, ← Matrix.charpoly_map _ (D.ntw.twist₂ a)]
    rfl

theorem allTriples_of_tripAll (h : TwistedTriples.TripAll D) : AllTriples D := fun a σ Sg hg hp =>
  (h a σ hg.symm).imp fun s hs => (triple_iff D a σ Sg hp s).1 hs

end GlobalTheory.TwistedSelmerCompare

end
