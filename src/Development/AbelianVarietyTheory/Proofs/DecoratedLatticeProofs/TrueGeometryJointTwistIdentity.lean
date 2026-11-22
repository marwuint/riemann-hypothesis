import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticExtensionCharactersPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero

noncomputable section

section General
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QVecJoin
open GlobalTheory.QVec GlobalTheory.LocMod.StepVec

theorem step_mid : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j, j + 1 < D.R.m → GlobalTheory.FinPl.Moves (c.V j) (B.b j) (B.Λ j) (v.N j) S → GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → B.b j ∈ GfC (c.V j) → B.b (j + 1) ∈ GfC (c.V (j + 1)) → IsSelfDualC _ (B.Λ j) → IsSelfDualC _ (B.Λ (j + 1)) → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V j).rank) χj vac (d : WO (c.V j) (c.V (j + 1)) →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V j) (c.V (j + 1)) sS sT (B.Λ j : Set _) (B.Λ (j + 1) : Set _) (B.β j) (B.β (j + 1)) LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ j) (B.Λ (j + 1)) S g → om (B.b j, B.b (j + 1)) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).eL j)) (om (B.b j, B.b (j + 1)) g) := by
  intro D c v B χ hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  have hn : ∀ i, ∃ n, j + n = (G i).s := fun i => ⟨(G i).s - j, by have := (G i).hs; omega⟩
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).eL j) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain ⟨n, hn⟩ := hn i
    exact ((E i).eL_at j n hn).1
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, -, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, -, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd j (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ j (n + 1) (by omega))) mS
        ((G i).latY j (n + 1) _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' (hv.sd (j + 1) hj) hmv' _ (eb.symm.trans (stdOrd _ _ (j + 1) n (by omega))) mT
        ((G i).latY (j + 1) n _) π' hπ⟩
  · obtain ⟨n, hn⟩ := hn i
    obtain ⟨ea, ha, mS⟩ := (G i).frame j (n + 1) (by omega)
    obtain ⟨eb, hb, mT⟩ := (G i).frame (j + 1) n (by omega)
    exact puts (G i).q hstep.1.2.inf hom hsd.1 hsd'.1 _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => _root_.GlobalTheory.QTw.LocFn.parPhi_component D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ _ _ _ mS mT ((E i).reg.1 j n hn) rfl ((E i).eL_at j n hn)

theorem step_top : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j (h : j + 2 * 0 + 2 = D.R.m), GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → GlobalTheory.FinPl.Moves c.T B.bT B.ΛT v.NT S → B.b (j + 1) ∈ GfC (c.V (j + 1)) → B.bT ∈ GfC c.T → IsSelfDualC _ (B.Λ (j + 1)) → IsSelfDualC _ B.ΛT → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V (j + 1)).rank) χj vac (d : WO (c.V (j + 1)) c.T →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V (j + 1)) c.T sS sT (B.Λ (j + 1) : Set _) (B.ΛT : Set _) (B.β (j + 1)) B.βT LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V (j + 1)) c.T χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ (j + 1)) B.ΛT S g → om (B.b (j + 1), B.bT) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).toAt.eT j h)) (om (B.b (j + 1), B.bT) g) := by
  intro D c v B χ hv r pl G E ξ Q S hinj hQ hS hres hrk j hj hmv hmv' hb hb' hsd hsd' sS sT LS χj vac d hPg hLr hvac hd hstep
    χS χT om hom g hg
  refine gen (fun i => (G i).q) pl (fun i => (G i).idem) (fun i => (G i).unit) hinj hQ hS hom hsd hsd' _ _ hPg hvac hd hstep
    (fun i => (E i).toAt.eT j hj) (fun i => ?_) (fun i π' hπ => ?_) (fun e he Tm hTm i => ?_) g hg
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    exact (E i).eLT_at.1
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    obtain ⟨ea, -, mS⟩ := (G i).frame ((G i).s + 1) 0 rfl
    obtain ⟨eb, -, mT⟩ := (G i).frameTop
    exact ⟨lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd (hv.sd _ (by omega)) hmv _ (ea.symm.trans (stdOrd _ _ _ 0 rfl)) mS
        ((G i).latY _ 0 _) π' hπ,
      lat_of_movedTo (G i).q ((hS _).2 ⟨i, rfl⟩) hsd' hv.sdT hmv' _ eb.symm mT (G i).latT π' hπ⟩
  · obtain rfl : j = (G i).s := by have := (G i).hs; omega
    obtain ⟨ea, ha, mS⟩ := (G i).frame ((G i).s + 1) 0 rfl
    obtain ⟨eb, hb, mT⟩ := (G i).frameTop
    exact puts (G i).q hstep.1.2.inf hom hsd.1 hsd'.1 _ _ he ((hQ _).2 ⟨i, rfl⟩) (G i).idem hstep.1.2.theta hTm ea eb
      (parPhi (E i).δ) (int_of_parPhi _) _
      (fun π' hπ hred N => _root_.GlobalTheory.QTw.LocFn.parPhi_component D _ (G i).q (pl i) π' hπ hred _ (E i).tame _ (hres i) _ _ _ _ _ _ _ _
        (hLr.trans (hrk i)) ea eb ha hb N) _ _ _ (Equiv.refl _) _ _ mS mT (E i).reg.2.1 rfl (E i).eLT_at

end GlobalTheory.QVecJoin
end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QVecJoin

theorem natCast_mem_under {D : D7} (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) :
    ((n : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal ↔ ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((n : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem false_of_coprime_mem {D : D7} (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hb : ((b : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  haveI : PP.asIdeal.IsPrime := PP.isPrime
  have ha' : ((a : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 ha
  have hb' : ((b : ℕ) : (𝓞 D.host.E) ⧸ PP.asIdeal) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hb
  exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_coprimes hab (ringChar.dvd ha') (ringChar.dvd hb'))

theorem isWeilDatum_cast {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

end GlobalTheory.QVecJoin

end
