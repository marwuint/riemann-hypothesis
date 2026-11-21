import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
import Formalism.WachLatticeTwists.HodgeTateChains.XiAdicFiltrationData
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Imports
import Formalism.WachLatticeTwists.HodgeTateChains.Statement
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement
import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
import Formalism.WachLatticeTwists.HodgeTateChains.GammaIterateMatrixCongruence
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

section H1

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module ℤ_[ℓ] M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul ℤ_[ℓ] M]
  {M' : Type} [AddCommGroup M'] [Module ℤ_[ℓ] M'] [TopologicalSpace M'] [ContinuousAdd M']
  [ContinuousConstSMul ℤ_[ℓ] M']

def Z1 (a : Representation ℤ_[ℓ] G M) : Submodule ℤ_[ℓ] (G → M) where
  carrier := {c | Continuous c ∧ ∀ g h, c (g * h) = c g + a g (c h)}
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨hc.add hd, fun g h => ?_⟩
    simp only [Pi.add_apply, hc', hd', map_add]
    abel
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := by
    rintro t c ⟨hc, hc'⟩
    exact ⟨hc.const_smul t, fun g h => by simp only [Pi.smul_apply, hc', smul_add, map_smul]⟩

def B1 (a : Representation ℤ_[ℓ] G M) : Submodule ℤ_[ℓ] (G → M) :=
  LinearMap.range (LinearMap.pi fun g => a g - LinearMap.id : M →ₗ[ℤ_[ℓ]] (G → M))

abbrev H1 (a : Representation ℤ_[ℓ] G M) : Type := Z1 a ⧸ (B1 a).comap (Z1 a).subtype

def H1.mk (a : Representation ℤ_[ℓ] G M) : Z1 a →ₗ[ℤ_[ℓ]] H1 a := Submodule.mkQ _

def H1.res {G' : Type} [Group G'] [TopologicalSpace G'] (a : Representation ℤ_[ℓ] G M) (p : G' →* G)
    (hp : Continuous p) : H1 a →ₗ[ℤ_[ℓ]] H1 (a.comp p) :=
  Submodule.mapQ _ _ ((LinearMap.funLeft ℤ_[ℓ] M p).restrict (by
    rintro c ⟨hc, hc'⟩
    refine ⟨hc.comp hp, fun g h => ?_⟩
    simp only [LinearMap.funLeft_apply, map_mul, hc', MonoidHom.comp_apply]) : Z1 a →ₗ[ℤ_[ℓ]] Z1 (a.comp p))
    (by
      rintro c ⟨m, hm⟩
      refine ⟨m, ?_⟩
      funext g
      exact congrFun hm (p g))

end H1

section SL

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] {OC : Type} [CommRing OC] [Algebra ℤ_[ℓ] OC]

structure SL (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) (r : ℕ) where
  Mx : G → Matrix (Fin r) (Fin r) OC
  one : Mx 1 = 1
  mul : ∀ g h, Mx (g * h) = (Mx h).map (actO g) * Mx g

variable {actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)} {r : ℕ}

variable [TopologicalSpace OC] [IsTopologicalRing OC] [ContinuousConstSMul ℤ_[ℓ] OC]

end SL

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
