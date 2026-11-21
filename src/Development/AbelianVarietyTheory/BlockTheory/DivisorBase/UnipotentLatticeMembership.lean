import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

open NumberField IsDedekindDomain Formalism.IndefR.Arith

section Clause

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)

def IsCoord {d : ℕ} (b : Fin d → WL) : Prop :=
  LinearIndependent LL b ∧ Submodule.span LL (Set.range b) = A.Wgood J0 lam0 eC

variable {A J0 lam0 eC}

end Clause

section Level

open Formalism.BasicNotions Formalism.L2.DIV

variable (D : D7) {LL : Type} [Field LL]

abbrev TypePl : Type := Σ k : Fin 2, D.nd.PlG k

instance finiteLevelGroupFintype : Fintype (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  Fintype.ofFinite _

end Level

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership
