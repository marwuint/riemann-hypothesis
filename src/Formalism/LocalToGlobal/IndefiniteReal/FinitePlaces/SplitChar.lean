import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StdCharExists
import Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
import Formalism.LocalToGlobal.IndefiniteReal.ExistsGADet
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin

namespace SplitChar

theorem exists_place_two (F : Type) [Field F] [NumberField F] :
    ∃ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal := by
  have h2 : ¬ IsUnit (2 : 𝓞 F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 by simp, Algebra.norm_algebraMap] at hn
    have hr : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    have hge : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 F) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Module.finrank ℤ (𝓞 F) := pow_le_pow_right₀ (by norm_num) hr
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have h2mem : (2 : 𝓞 F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h0 : (2 : 𝓞 F) = 0 := (Submodule.mem_bot _).mp h2mem
    have h0' : (2 : F) = 0 := by
      have := congrArg (algebraMap (𝓞 F) F) h0
      rwa [map_ofNat, map_zero] at this
    exact two_ne_zero h0'
  exact ⟨⟨M, hM.isPrime, hM0⟩, h2mem⟩

theorem exists_splitIdem_D (D : D7) : ∃ e, IsSplitIdem D e := by
  obtain ⟨v, hv⟩ := exists_place_two D.host.F
  obtain ⟨e, ε, he, -, -⟩ := twoSplitIdem D v hv
  exact ⟨e, he⟩

variable {D : D7}

def RA (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E) :
    Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  proj (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv)

theorem haA (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) :
    incA D ainv * hsq (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) = 1 := by
  rw [← hsq_map (incA D) (flipTwoThree.sigE D) (cA D) (fun a => (flipTwoThree.cA_incA' a).symm), ← map_mul, ha, map_one]

theorem hainvA (ainv : D.host.E) (hainv : flipTwoThree.sigE D ainv = ainv) : cA D (incA D ainv) = incA D ainv := by
  rw [flipTwoThree.cA_incA', hainv]

def secM (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E) (x : AE D) :
    Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
  1 + (x - 1) • RA V u ainv

theorem secM_unitary (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) (x : AE D)
    (hx : cA D x * x = 1) :
    ((secM V u ainv x).map (cA D))ᵀ * V.gram.map (incA D) * secM V u ainv x = V.gram.map (incA D) :=
  proj_unitary (cA D) Formalism.L2.Theta.cA_cA (V.gram.map (incA D)) (flipTwoThree.gramA_herm V) _ _ (haA V u ainv ha)
    (hainvA ainv hainv) x hx

theorem secM_det (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (x : AE D) : (secM V u ainv x).det = x :=
  det_proj' (cA D) _ _ _ (haA V u ainv ha) x

theorem unitary_one_conj_mul_self (x : FirstPropositionFrame D) : cA D (((x : (AE D)ˣ)) : AE D) * (((x : (AE D)ˣ)) : AE D) = 1 := by
  rw [mul_comm]; exact x.2

def secG (V : HSp D) (u : Fin V.rank → D.host.E) (ainv : D.host.E)
    (ha : ainv * hsq (flipTwoThree.sigE D) V.gram u = 1) (hainv : flipTwoThree.sigE D ainv = ainv) (x : FirstPropositionFrame D) : GA D V :=
  flipTwoThree.mkGA V (secM V u ainv ((x : (AE D)ˣ) : AE D)) (secM_unitary V u ainv ha hainv _ (unitary_one_conj_mul_self x))
    (by rw [secM_det V u ainv ha]; exact (x : (AE D)ˣ).isUnit)

end SplitChar

end Formalism.IndefR.Fin

end
