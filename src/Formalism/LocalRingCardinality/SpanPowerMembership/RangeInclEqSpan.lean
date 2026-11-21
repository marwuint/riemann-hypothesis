import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalRingCardinality.SpanPowerMembership.BasisOfBasisF

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

def scalAct {Γ : Type} [Group Γ] (K V : Type) [Field K] [AddCommGroup V] [Module K V] (ψ : Γ →* Kˣ) :
    Γ →* (V ≃ₗ[K] V) := (DistribMulAction.toModuleAut K V).comp ψ

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

set_option synthInstance.maxHeartbeats 400000 in

structure NzIn (C : TwCore R H what₂ LL0 N) : Type 1 where
  eA : ∀ i, Bool → MonoidAlgebra (FractionRing (C.O i)) (G0g N)
  eL : G0g N → LL0
  eA_def : ∀ i b (g : G0g N), (eA i b).coeff g =
    IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i) ((if b then C.emb0 i else C.emb0b i) (eL g))
  eA_idem : ∀ i b, eA i b * eA i b = eA i b
  eA_central : ∀ i b x, eA i b * x = x * eA i b
  Psi : ∀ i, G0g N →* (FractionRing (C.O i))ˣ
  hPsi : ∀ i b (V : Type) [AddCommGroup V] [Module (FractionRing (C.O i)) V],
    MonoidAlgebra.lift (FractionRing (C.O i)) (Module.End (FractionRing (C.O i)) V) (G0g N)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (scalAct _ V (Psi i))) (eA i b) = 1
  ix : ℕ → Type
  [ixF : ∀ j, Fintype (ix j)]
  [ixD : ∀ j, DecidableEq (ix j)]
  ix_out : ∀ j, Nonempty (ix j) → 1 ≤ j ∧ j ≤ R.m
  ixM : ℕ → Type
  [ixMF : ∀ j, Fintype (ixM j)]
  [ixMD : ∀ j, DecidableEq (ixM j)]
  rM : ∀ j, ix j → ixM j

attribute [instance] NzIn.ixF NzIn.ixD NzIn.ixMF NzIn.ixMD

namespace TwCore

variable (C : TwCore R H what₂ LL0 N) (I : NzIn C)

def SigN : Type := {p : Fin (R.m + 1) × Bool // 1 ≤ p.1.1 ∧ Nonempty (I.ix p.1.1)}

instance : Finite (SigN C I) := inferInstanceAs (Finite {p : Fin (R.m + 1) × Bool // _})

variable [hL : IsEmpty N.Loc]

instance (i k) : Algebra.IsIntegral (C.O i) (C.Ok i k) :=
  haveI := C.Ok_fin i k
  inferInstance

end TwCore

end Formalism.BasicNotions.Examples₂
