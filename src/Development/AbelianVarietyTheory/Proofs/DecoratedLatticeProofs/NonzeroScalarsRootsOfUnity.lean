import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOComb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroLocalScalars
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStep
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.StepVacForm

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem theta_comb (hψ : IsStdChar D ψ (-1)) {c : WO S T →₀ ℂ} (hc : IsFinComb c) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hc u hu))

theorem comb_smul (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem vac_mono {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem real_fock {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {e : WO S T →₀ ℂ} (he : IsFinComb e) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (P) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T) :
    om (a, a') (pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P) =
      comb ψ S T e (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) := by
  have h1 : om (1, 1) (comb ψ S T e f₀) = (1 : ℂ) • comb ψ S T e f₀ := by
    rw [one_smul, show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply]
  have := (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT e f₀ _ 1 he hf₀ (theta_comb hW.std he hf₀)
    1 (one_mem _) 1 (one_mem _) h1 P a ha a' ha').1
  rwa [mul_one, mul_one, one_smul] at this

theorem step {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {P Q : GlobalTheory.FinPl.Pl D → Prop} (hd : ∀ p, P p → ¬ Q p) {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} {vac : WO S T → ℂ}
    (hv : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) vac) {dG dQ eG eQ : WO S T →₀ ℂ} (hdG : GlobalTheory.FinPl.CombAt P dG)
    (hdQ : GlobalTheory.FinPl.CombAt Q dQ) (heG : GlobalTheory.FinPl.CombAt P eG) (heQ : GlobalTheory.FinPl.CombAt Q eQ)
    {b : GA D S} (hb : b ∈ GfC S) {b' : GA D T} (hb' : b' ∈ GfC T) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T)
    (hQ : ∀ g, GlobalTheory.FinPl.Vac ψ S T LS LT Q g → om (b, b') (comb ψ S T dQ g) = comb ψ S T eQ (om (b, b') g))
    (Pol) {c : ℂ} {Ψ : WO S T → ℂ}
    (hG : IsThetaFunO ψ S T (comb ψ S T dG (pureTensorO ψ θ S T sS sT BS BT vac Pol)) →
      om (a * b, a' * b') (comb ψ S T dG (pureTensorO ψ θ S T sS sT BS BT vac Pol)) = c • comb ψ S T eG Ψ) :
    om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT (comb ψ S T dQ (comb ψ S T dG vac)) Pol) =
      c • comb ψ S T eG (comb ψ S T eQ Ψ) := by
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hPQ := GlobalTheory.DisjComb.main D ψ hψ S T P Q hd
  have hQP := GlobalTheory.DisjComb.main D ψ hψ S T Q P (fun p h h' => hd p h' h)
  have fG : IsFinComb dG := (hPQ.2.1 dG hdG).1
  have fQ : IsFinComb dQ := (hQP.2.1 dQ hdQ).1
  have h1 : om (1, 1) (comb ψ S T dG vac) = (1 : ℂ) • comb ψ S T dG vac := by
    rw [one_smul, show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply]
  have hvac := fun a ha a' ha' => (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT dG vac _ 1 fG hv.1
    (theta_comb hψ fG hv.1) 1 (one_mem _) 1 (one_mem _) h1 Pol a ha a' ha').2 LS LT hv
  have hth : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT vac Pol) := by
    have := (hvac 1 (one_mem _) 1 (one_mem _)).1
    rwa [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply] at this
  have hg := (hPQ.2.1 dG hdG).2 LS LT _ (vac_mono Q (hvac a ha a' ha'))
  have e1 : ((a * b, a' * b') : GA D S × GA D T) = (b, b') * (a, a') := by
    rw [Formalism.IndefR.Eqv.Act.comm_inf_fin ha hb, Formalism.IndefR.Eqv.Act.comm_inf_fin ha' hb']
    rfl
  have hG' := hG (theta_comb hψ fG hth)
  rw [e1, map_mul, Module.End.mul_apply, GlobalTheory.FrComb.om_comb hW ha ha' fG hth] at hG'
  rw [e1, map_mul, Module.End.mul_apply, real_fock hθ hW sS sT BS BT fQ (theta_comb hψ fG hv.1) Pol ha ha',
    real_fock hθ hW sS sT BS BT fG hv.1 Pol ha ha', hQ _ hg, hG', comb_smul, hPQ.1 eG eQ heG heQ]

end Gen

theorem under_ne {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) {PP PP' : Pl D.host.E} (h : PP ∈ L.Pg)
    (h' : PP' ∈ L.Q t) : PP.under (𝓞 D.host.F) ≠ PP'.under (𝓞 D.host.F) := by
  intro e
  obtain ⟨i, hi⟩ := (hL.Pg PP).1 h
  obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hL.Q_pl t PP' h'
  have hg : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h0 := L.C.P.pb_over i
    rw [← hi] at h0
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h0
    rwa [map_natCast] at h2
  have hq' : (q : 𝓞 D.host.E) ∈ PP'.asIdeal := by
    have h1 : Nat.card (kP PP') • (1 : kP PP') = 0 := card_nsmul_eq_zero'
    rw [hcard, nsmul_one] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_natCast _ q).trans h1)
  have hqF : (q : 𝓞 D.host.F) ∈ (PP'.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) q ∈ PP'.asIdeal
    rwa [map_natCast]
  rw [← e] at hqF
  have hqP : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) q ∈ PP.asIdeal := hqF
    rwa [map_natCast] at h2
  obtain ⟨a, b, hab⟩ : IsCoprime ((D.host.g i : ℕ) : 𝓞 D.host.E) q :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime i) hq).2 fun h => hqg i h.symm)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hg) (PP.asIdeal.mul_mem_left _ hqP)))

end GlobalTheory.StepVacForm

end
