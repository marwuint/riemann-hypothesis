import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWildInertiaGeneratingCyclotomicValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionSetting

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
  GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OChoose

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
    rw [show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap] at h1
    have h2 := Int.isUnit_iff_natAbs_eq.1 h1
    have h3 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases Nat.pow_eq_one.1 h2 with h | h
    · exact hp.one_lt.ne' h
    · exact h3.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

theorem exists_wild_inertia_cyclotomic_generator (D : D7) (i : D.nd.Loc) : ∃ g0, IsWildInertiaCyclotomicElement D.nd i g0 := by
  by_cases ht : ∃ k, D.nd.l i = D.host.g k
  · obtain ⟨k, hk⟩ := ht
    obtain ⟨g0, h1, h2, h3⟩ := GlobalTheory.T.exists_wildInertia_generating_cyclotomicValue D i k hk
    exact ⟨g0, ⟨h1, h2⟩, fun _ => h3⟩
  · obtain ⟨w, hw⟩ := placesOver_nonempty D.host.E (D.nd.l i) (D.nd.lPrime i).out
    obtain ⟨g, hg, hc⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
    exact ⟨g, ⟨⟨w, hw, hg⟩, 1, by simpa using hc⟩, fun h => absurd h ht⟩

theorem exists_fin_roots {p : ℂ[X]} {t : ℕ} (hm : p.Monic) (hd : p.natDegree = t) :
    ∃ α : Fin t → ℂ, (∀ c, α c ∈ p.roots) ∧ p = ∏ c, (X - C (α c)) := by
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hp := (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard).symm
  obtain ⟨l, hl⟩ : ∃ l : List ℂ, (l : Multiset ℂ) = p.roots := Quotient.exists_rep _
  have hlen : l.length = t := by rw [← hd, ← hcard, ← hl, Multiset.coe_card]
  subst hlen
  refine ⟨fun c => l.get c, fun c => hl ▸ Multiset.mem_coe.2 (List.get_mem l c), ?_⟩
  conv_lhs => rw [hp, ← hl]
  rw [Multiset.map_coe, Multiset.prod_coe]
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

theorem blockPol_iota (D : D7) (i : D.nd.Loc) {rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i)) {π : D.nd.X i} {g0 : GE D.nd}
    {L : ℕ} {eB e1 X0 : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hc : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice D.R.t (D.nd.T i) rep ρ (D.nd.chi i) π g0 L eB e1 X0) (x : D.nd.X i) :
    ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO D.nd D.naut i)).Monic ∧
      ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO D.nd D.naut i)).natDegree = D.R.t := by
  obtain ⟨hr, -, -, hX1, hX2, -⟩ := GlobalTheory.ConsExists.choice_facts hS.1 hS.2.2.2.1 hc
  obtain ⟨hm, hd⟩ := GlobalTheory.ConsExists.blockPol_monic (congrFun hc.1.2.2.1 x) (hr x) (congrFun hX1 x) (congrFun hX2 x)
  have hinj : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.toFr (D.nd.O i)) :=
    IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have hm' := Polynomial.monic_of_injective hinj hm
  rw [Polynomial.natDegree_map_eq_of_injective hinj] at hd
  exact ⟨hm'.map _, (hm'.natDegree_map _).trans hd⟩

end GlobalTheory.OChoose

end
