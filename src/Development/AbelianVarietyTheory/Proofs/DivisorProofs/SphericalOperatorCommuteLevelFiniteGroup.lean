import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeKeepsGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levChi_mul {k k' : GA D V} (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  unfold levChi
  rw [← Units.val_mul, MonoidHom.map_mul]
  exact congrArg Units.val ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {R : Finset (GA D V)}

theorem hasType_heckeLin (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) : HasType V β L (heckeLin V R F) :=
  GlobalTheory.SphericalOps.level_heckeLin (fun _ hk _ hk' => levChi_mul hk hk')
    (fun e f _ hI => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hI hN hPP).2.2) hR hF

theorem sphericalOperator_commute_levelFiniteGroup (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) (x : Formalism.L2.DIV.G0 L.Pg L.r) :
    actG0 V β L x (heckeLin V R F) = heckeLin V R (actG0 V β L x F) := by
  have hG := hasType_heckeLin hB hN hPP hR hF
  obtain ⟨e, f, ϖ, α, -, hI, -, -, -, hJ, hχ, -, -, hRs, -⟩ := hR
  unfold actG0
  split_ifs with hk
  swap
  · exact (map_zero _).symm
  have hκ := hk.choose_spec
  generalize hk.choose = κ at hκ ⊢
  obtain ⟨a1, -, a3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hI hN hPP
  obtain ⟨k₁, m₁, k₂, -, s₁, s₂, rfl⟩ := a3 κ ⟨hκ.1, hκ.2.1, Subgroup.mem_top _⟩
  have m : k₁ ∈ levG V β L := (hJ k₁ s₁).2 ((a1 k₁ s₁).1 m₁)
  obtain ⟨hff, hcf, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hI
  have hc : ∀ a, SuppF V f a → Commute a k₂ := fun a ha =>
    ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f hff hcf).2.2 (1 - f) a k₂ (by rw [mul_sub, mul_one, hff, sub_self]) ha s₂
  have key : ∀ G : GA D V → ℂ, HasType V β L G → ∀ h, G (h * (k₁ * k₂)) = G (h * k₂) := fun G hG h => by
    rw [(hc k₁ s₁).eq, ← mul_assoc, hG k₁ m, hχ k₁ m s₁, one_mul]
  funext h
  rw [key _ hG]
  show _ * ∑ γ ∈ R, F (h * k₂ * γ) = ∑ γ ∈ R, _ * F (h * γ * (k₁ * k₂))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [key F hF, mul_assoc h γ, (hc γ (hRs γ hγ)).eq, mul_assoc h]

end GlobalTheory.HeckeKeepsGood
