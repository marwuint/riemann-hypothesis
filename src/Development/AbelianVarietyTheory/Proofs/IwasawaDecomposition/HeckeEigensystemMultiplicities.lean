import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceOutsideNonHyperspecialOfLocalisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicHeckeOperatorHyperspecialActsByScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeMultiplicityEqFinrankJointEigenspace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankJointEigenspaceCoefficientFieldComplex
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutPts

theorem l0 : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := GlobalTheory.T.splitPlace_outside_nonHyperspecial_of_localisation
theorem l1 : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := _root_.GlobalTheory.IsoTypScalar.main
theorem l2a : ∀ (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ) (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i), X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w)) (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := _root_.GlobalTheory.HeightCounting.mult_eq_finrank_jointEig
theorem l2b : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := _root_.GlobalTheory.PtLocalEig.eig_dim

theorem mt_tr {D : D7} (M : MtFam D) (Pr : ∀ (μ : D.what₂.Tup) (j : ℕ), MtReal D μ j → Prop) {μ μ' : D.what₂.Tup}
    {j j' : ℕ} (hμ : μ = μ') (hj : j = j') (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) :
    Pr μ j (M μ j a1 a2) → Pr μ' j' (M μ' j' b1 b2) := by
  subst hμ hj; exact id

theorem genAt_iff' {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    {X : LocNd (lay0 D)} {T : LocTw X} (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.what₂.places.resChar (X.nd.w i)) (Sp.B.Qc (X.nd.j i) (X.nd.w i)) v k ↔
      (SplitOut X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have h : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hl : X.nd.l i = D.what₂.places.resChar (X.nd.w i) := (X.nd.w_l i).symm
  have hS : v ∈ X.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar (X.nd.w i)) := by
    rw [X.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, Sp.Q_eq _ _ i h, hl]
  tauto

theorem mem_iSup_iff {V Wf : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Wf] [Module ℂ Wf] {ι : Type}
    [Finite ι] (real : V →ₗ[ℂ] Wf) (hreal : Function.Injective real) (typ : ι → Submodule ℂ V)
    (hind : iSupIndep typ) (htop : ⨆ P, typ P = ⊤) {Par : Type} (Good : Par → Prop) (op : Par → Wf → Wf)
    (hlin : ∀ p, Good p → ∀ (c : ℂ) (f f' : Wf), op p (c • f + f') = c • op p f + op p f')
    (hsc : ∀ P p, Good p → ∃ c : ℂ, ∀ y ∈ typ P, op p (real y) = c • real y) (lam : Par → ℂ) (Q : ι → Prop)
    (hQ : ∀ P, Q P ↔ ∀ p, Good p → ∀ y ∈ typ P, op p (real y) = lam p • real y) (y : V) :
    y ∈ (⨆ P ∈ {P | Q P}, typ P) ↔ ∀ p, Good p → op p (real y) = lam p • real y := by
  classical
  have hop0 : ∀ p, Good p → op p 0 = 0 := fun p hp => by
    have h := hlin p hp 1 0 0
    rw [one_smul, add_zero, one_smul] at h
    exact (add_eq_left.1 h.symm)
  have hopadd : ∀ p, Good p → ∀ f f' : Wf, op p (f + f') = op p f + op p f' := fun p hp f f' => by
    simpa using hlin p hp 1 f f'
  have hopsmul : ∀ p, Good p → ∀ (c : ℂ) (f : Wf), op p (c • f) = c • op p f := fun p hp c f => by
    simpa [hop0 p hp] using hlin p hp c f 0
  let Es : Submodule ℂ V :=
    { carrier := {y | ∀ p, Good p → op p (real y) = lam p • real y}
      zero_mem' := fun p hp => by simp [hop0 p hp]
      add_mem' := fun {a b} ha hb p hp => by
        simp only [map_add, hopadd p hp, ha p hp, hb p hp, smul_add]
      smul_mem' := fun c a ha p hp => by
        simp only [map_smul, hopsmul p hp, ha p hp, smul_comm c (lam p)] }
  show y ∈ _ ↔ y ∈ Es
  constructor
  · intro hy
    refine (iSup₂_le fun P hP => ?_ : (⨆ P ∈ {P | Q P}, typ P) ≤ Es) hy
    intro z hz p hp
    exact (hQ P).1 hP p hp z hz
  · intro hy
    have hy' : y ∈ ⨆ P, typ P := by rw [htop]; trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp typ y).1 hy'
    rw [← hsum]
    refine Submodule.finsuppSum_mem _ _ _ _ fun P hPs => ?_
    by_cases h0 : f P = 0
    · rw [h0]; exact Submodule.zero_mem _
    refine (le_iSup₂ (f := fun P (_ : P ∈ {P | Q P}) => typ P) P ?_) (hf P)
    show Q P
    refine (hQ P).2 fun p hp => ?_
    obtain ⟨c, hc⟩ := hsc P p hp
    choose cc hcc using fun P' => hsc P' p hp

    have hz : ∑ P' ∈ f.support, (cc P' - lam p) • f P' = 0 := by
      apply hreal
      rw [map_zero, map_sum]
      have e1 : ∀ P' ∈ f.support, real ((cc P' - lam p) • f P') = op p (real (f P')) - lam p • real (f P') := by
        intro P' _
        rw [map_smul, hcc P' _ (hf P'), sub_smul]
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.smul_sum]
      have e2 : ∀ s : Finset ι, op p (real (∑ P' ∈ s, f P')) = ∑ P' ∈ s, op p (real (f P')) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [hop0 p hp]
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, hopadd p hp, ih]
      have e3 : (∑ P' ∈ f.support, f P') = y := hsum
      have e4 : ∑ P' ∈ f.support, op p (real (f P')) = op p (real y) := by rw [← e2, e3]
      have e5 : ∑ P' ∈ f.support, real (f P') = real y := by rw [← e3, map_sum]
      rw [e4, e5, hy p hp, sub_self]
    have hz' := ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero typ).1 hind) f.support
      (fun P' => (cc P' - lam p) • f P') (fun P' _ => Submodule.smul_mem _ _ (hf P')) hz P
      (Finsupp.mem_support_iff.2 h0)
    have hcl : cc P = lam p := by
      rcases smul_eq_zero.1 hz' with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h h0
    intro z hz
    rw [hcc P z hz, hcl]

end GlobalTheory.AutPts

namespace GlobalTheory.AutPts

end GlobalTheory.AutPts
