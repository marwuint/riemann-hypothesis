import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepVanishTargetCoreLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.FinPl

theorem suppSecond_holds : ∀ D : D7, SuppSecond D := by
  intro D k _ _ _ _ ι p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL Λ P a b a' sh sd₂ Φ₁ Φ₂ hΦ₁ hΦ₂
  have tameP : ∀ v, P v → Tame D v := fun v hv => (sh.good v hv).tame
  refine ⟨?_, fun h₁ hh₁ => ⟨?_, ?_⟩⟩
  · exact _root_.GlobalTheory.VacFixP.vac_fix_on D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ P
      (fun v hv => ⟨(sh.good v hv).sdW, sd₂, tameP v hv, (sh.unr v hv).2.1, (sh.unr v hv).2.2⟩) Φ₂ hΦ₂
  · intro h₂ hh₂
    exact _root_.GlobalTheory.VacSecondPf.vac_second D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ P (fun v hv => ⟨sh.adapt v hv, (sh.unr v hv).2⟩) Φ₂ hΦ₂
      h₁ hh₁ h₂ hh₂
  · intro g hg φ hφ h₂ hne
    have key := _root_.GlobalTheory.FinPl.placesToAdeles_all D B'.V Λ.L₂ P sd₂ (besGrp B'.d B'.o) h₂ ?_
    · exact key
    intro v hv
    obtain ⟨hv', hhv, h', hh', rfl⟩ := _root_.GlobalTheory.FinPl.decompAt D B'.V h₂ v
    refine ⟨hv', hhv, h', hh', rfl, ?_⟩
    have gd := sh.good v hv
    have ad := sh.adapt v hv
    have sdL₁ : IsSelfDualC J.W Λ.L₁ := gd.sdW

    have hΦ₂v : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) Φ₂ :=
      ((_root_.GlobalTheory.VacLoc.vac_loc D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ P tameP Φ₂).1.mp hΦ₂).2 v hv
    set f := s₂.om (h₁, h') Φ₂ with hfdef
    have hf : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) f :=
      (_root_.GlobalTheory.VacLoc.vac_loc D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ (· = v)
        (fun w hw => hw ▸ gd.tame) Φ₂).2.1 hΦ₂v h₁ (_root_.GlobalTheory.FinPl.grpOff_anti D J.W P (· = v) (fun w hw => hw ▸ hv) hh₁) h' hh'

    set Ξ₁ := flatBF s₁ (s₁.om (g, h₁) Φ₁) with hΞ₁def
    have hΞ₁P : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ P Ξ₁ :=
      ((_root_.GlobalTheory.FinPl.suppFirst_all D ψ (σ + 1) B J s₁ Λ.L₀ Λ.M₀ Λ.L₁ Λ.M₁ P (fun w hw => sh.good w hw)
        (fun w hw => (sh.unr w hw).1) sdL₁ Φ₁ hΦ₁).2 g hg).2 h₁ hh₁
    have hΞ₁ : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ (· = v) Ξ₁ :=
      ((_root_.GlobalTheory.VacLoc.vac_loc D ψ B.V₀ J.W₀ s₁.χV s₁.χW s₁.om₀ s₁.weil₀ Λ.M₀ Λ.M₁ gd.sdV₀ gd.sdW₀ P tameP Ξ₁).1.mp
        hΞ₁P).2 v hv

    have hom : s₂.om (h₁, hv' * h') Φ₂ = s₂.om (1, hv') f := by
      rw [hfdef, show ((h₁, hv' * h') : GA D J.W × GA D B'.V) = (1, hv') * (h₁, h') by simp, map_mul]
      rfl
    have hand_eq : Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (hv' * h') =
        hand0 s₁ s₂ l vL φ Ξ₁ (flatFB s₂ (s₂.om (1, hv') f)) := by
      simp only [Chain.hand, hand0, hom, hΞ₁def]
    rw [hand_eq] at hne
    have hne' : flatFB s₂ (s₂.om (1, hv') f) ≠ 0 := by
      intro h0
      apply hne
      rw [h0, show (0 : WO J.W₀ B'.V₀ → ℂ) = (0 : ℂ) • (0 : WO J.W₀ B'.V₀ → ℂ) by simp, _root_.GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel, zero_smul]
    obtain ⟨nn, hnF, hnv, γ, hγ, κ, hκ, hdec, hγp⟩ :=
      (_root_.GlobalTheory.FinPl.supportShift D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ v ad (sh.unr v hv).2 (flatFB s₂)
        ((_root_.GlobalTheory.FinPl.flatLaws_all D ψ (· = v)).2 σ J B' s₂) ((_root_.GlobalTheory.FlatShiftPf.flatShift D ψ (· = v)).2 σ J B' s₂) f hf).2 hv' hhv hne'
    by_cases hgl : ∃ i, v = (p i).v
    · obtain ⟨i, rfl⟩ := hgl
      rcases GlobalTheory.T.threeOrbits_gluedCore_atPlace D k (p i) n'' q σ B' Λ.M₂ (a'.α i) (a'.α₀ i) (a'.P i) ad.sdW₀ (sh.gl' i) γ hγ hγp with
        ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ | ⟨Λ₀, hΛ₀, hmov⟩
      · obtain ⟨r, hr, hrv, κ', hκ', heq⟩ :=
          _root_.GlobalTheory.FinPl.OrbitCoset.orbit_coset D σ B' Λ.L₂ Λ.M₂ (p i).v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
        exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩
      · exfalso
        apply hne
        obtain ⟨M, sdM, hMov, hvacM⟩ :=
          _root_.GlobalTheory.FinPl.movedVac D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ (p i).v ad (sh.unr _ hv).2 f hf γ hγ
        have hlat : (a'.α₀ i).IsLat M (lastKer Λ₀) ∨ (a'.α₀ i).IsLat M (lastPair q Λ₀).lat := by
          rcases hmov with h | h
          · exact Or.inl (_root_.GlobalTheory.FinPl.Frame.isLat_of_isLatMoved D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
          · exact Or.inr (_root_.GlobalTheory.FinPl.Frame.isLat_of_isLatMoved D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
        obtain ⟨φf, hφf, hφP⟩ := hφ.2 i
        have hz := _root_.GlobalTheory.FinPl.vertexGlued_vanish_lastLat D k (p i) n n' n'' q ψ σ B J B' s₁ s₂ l vL s₂.weil.std (sh.unr _ hv).1
          (sh.unr _ hv).2 Λ.M₀ Λ.M₁ M (a.α i) (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (a.P i) (b.Q i) Λ₀ gd.sdV₀ gd.sdW₀
          sdM (sh.gl i) (sh.mid i) (sh.gl' i).sum hlat Ξ₁ _ hΞ₁ hvacM φf hφf
        rw [hφP] at hz
        rw [hdec, _root_.GlobalTheory.FinPl.flatFB_om_shift D ψ σ J B' s₂ Λ.L₁ Λ.L₂ (p i).v sdL₁ sd₂ gd.tame (sh.unr _ hv).2 f hf nn hnF hnv _ κ hκ,
          _root_.GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel, hz, smul_zero]
    · obtain ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ := _root_.GlobalTheory.FinPl.SplitOrbit.orbitSplit D σ B' Λ.M₂ v gd.tame ad.sdW₀
        (sh.split v hv fun i h => hgl ⟨i, h⟩) γ hγ hγp
      obtain ⟨r, hr, hrv, κ', hκ', heq⟩ := _root_.GlobalTheory.FinPl.OrbitCoset.orbit_coset D σ B' Λ.L₂ Λ.M₂ v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
      exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩

end GlobalTheory.FinPl
