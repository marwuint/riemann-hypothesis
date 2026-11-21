import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.PinModel

variable {D : D7} {u : D.what₂.Word}

theorem exists_finM (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a ∈ GfC V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, ha, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ha, ?_⟩
  have e2 : (finE V a : GL _ _) = y.1 := congrArg Subtype.val e
  rw [← e2]
  rfl

theorem exists_transport_adelic_correction {X : HidaSetting D} {F : Formalism.L2.Forms.Forms0 D u} (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    ∃ a, IsTransportAdelicCorrection tr a := by
  obtain ⟨a, ha, e⟩ := exists_finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) tr.h0
  exact ⟨a, ha, e⟩

theorem exists_isTypePlaces : ∃ Pg : Finset (Pl D.host.E), GlobalTheory.Core.Mi.IsTypePlaces Pg := by
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ PP : Pl D.host.E, PP.under (𝓞 D.host.F) = v := fun v => by
    have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    refine ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, ?_⟩
    exact HeightOneSpectrum.ext hQ'.over.symm
  choose s hs using key
  have hne : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hfin : {v : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)})
      (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  refine ⟨hfin.toFinset.image s, ?_, ?_⟩
  · intro PP hPP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
    have hv' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := hfin.mem_toFinset.1 hv
    rw [← hs v] at hv'
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (s v).asIdeal := hv'
    rwa [map_natCast] at h2
  · intro v hv
    refine ⟨s v, ⟨Finset.mem_image.2 ⟨v, hfin.mem_toFinset.2 hv, rfl⟩, hs v⟩, ?_⟩
    rintro PP ⟨hPP, e⟩
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hPP
    rw [hs w] at e
    rw [e]

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)

end GlobalTheory.Core.Mi.PinModel

end
