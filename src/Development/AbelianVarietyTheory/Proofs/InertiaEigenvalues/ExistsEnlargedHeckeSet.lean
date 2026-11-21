import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSbLayer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Raw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_sb_raw (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (YS : NExpRealS Rl cG (ratDatR Rl cG kKs hk)) (H : NExpRealH Rl cG (ratDatR Rl cG kKs hk) YS)
    (hX : NExpHeckeRowX Rl cG _ YS H fun _ => LinearMap.id) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hne : Nonempty D.ntw.Tw)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) :
    ∃ Sb' : Finset (PlE D.host), Sb ⊆ Sb' ∧ (∀ i, Sb' ⊆ D.ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low D Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd Rl cG kKs hk Sb' H.hL := by
  classical
  obtain ⟨i₀⟩ := hne
  refine ⟨(D.ntw.S0 i₀).filter (fun P => ∀ i, P ∈ D.ntw.S0 i), fun P hP => Finset.mem_filter.2 ⟨hSb i₀ hP, fun i => hSb i hP⟩,
    fun i P hP => (Finset.mem_filter.1 hP).2 i, ?_, ?_⟩
  · intro P hP
    have hall : ∀ i, P ∈ D.ntw.S0 i := by
      intro i
      rw [Nat.cast_mul, Nat.cast_mul] at hP
      rcases P.isPrime.mem_or_mem hP with h | h
      · exact hS02 i h
      · rcases P.isPrime.mem_or_mem h with h | h
        · exact D.ntw.placesOver_subset_exceptional i 0 h
        · exact D.ntw.placesOver_subset_exceptional i 1 h
    exact Finset.mem_filter.2 ⟨hall i₀, hall⟩
  · intro j k P α Rr h1 h2 hd x
    have hi' : ∃ i', P ∉ D.ntw.S0 i' := by
      by_contra hc
      push_neg at hc
      exact hd.offS (Finset.mem_filter.2 ⟨hc i₀, hc⟩)
    obtain ⟨i', hi'⟩ := hi'
    obtain ⟨-, -, -, -, hso, -, -, -⟩ :=
      GlobalTheory.ConjPlaceOff.exists_conj_off D (D.ntw.S0 i') Rl.Sb P (hS0c i') (hS02 i') (hS0b i') hd.split hi'
    have hj : (idxOf D j : ℕ) + 1 = j := by simp only [idxOf]; omega
    let y : (ratDatR Rl cG kKs hk).WL ((idxOf D j : ℕ) + 1) := (YS.fi (idxOf D j)).e.symm x
    have hy : (YS.fi (idxOf D j)).e y = x := LinearEquiv.apply_symm_apply _ _
    have key : ∀ n (hn : n = j) (z : (ratDatR Rl cG kKs hk).WL n), HEq z x → HEq (H.hL n k P z) (H.hL j k P x) := by
      intro n hn z hz
      subst hn
      rw [eq_of_heq hz]
    have h3 : HEq ((YS.fi (idxOf D j)).e (H.hL ((idxOf D j : ℕ) + 1) k P y)) (H.hL j k P x) :=
      (hfi _ _).trans (key _ hj y ((hy ▸ hfi _ y).symm))
    have ht := hX.tie (idxOf D j) k P hd.split hso ⟨i', hi'⟩ hd.odd hd.le α Rr hd.elt hd.reps y rfl
    rw [eq_of_heq h3, hy] at ht
    exact ht

end Raw

end GlobalTheory.HeckeSbLayer

namespace GlobalTheory.HeckeSbLayer

end GlobalTheory.HeckeSbLayer

end
