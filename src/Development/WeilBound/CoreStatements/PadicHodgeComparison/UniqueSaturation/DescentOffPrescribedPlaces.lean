import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.EigInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.D

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def BCAt (π : CuspSub E n) (σ : Submodule ℂ (UA E n → ℂ)) (w : Pl E) : Prop :=
  ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt σ w s ϖ q α → (CG.mk π).HasSat w (GlobalTheory.LGrp.bcParam n α)

def IsExtOf2 (π : CuspSub E n) (w : Pl E) (β : Fin (n / 2) → ℂˣ) : Prop :=
  (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧ (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧
    ∃ α, (CG.mk π).HasSat w (GlobalTheory.LGrp.bcParam n α) ∧ GlobalTheory.LGrp.WeylConjU α β

def RigidAt (π : CuspSub E n) (T₀ : Finset (Pl E)) : Prop :=
    ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
      (∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)) →
      (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → Comp σ w τ) →
    ∀ D : Pre E n, PositivityTheory.Rg.BcB.One.Base σ D → (∀ w, IsSplitAt w → D.SplitAt σ w) → D.ThetaStable →
      (∀ w, ¬ IsSplitAt w → ∃ B, D.Sat w B) →
      (∀ w ∈ T₀, ∀ B, (CG.mk π).HasSat w B → D.Sat w B) →
      ∀ w, ¬ IsSplitAt w → ∀ B, D.Sat w B → (CG.mk π).HasSat w B

open PositivityTheory.Rg.Rs

end PositivityTheory.AutomorphicGaloisHodgeTate.D

end
