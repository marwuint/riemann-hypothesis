import Mathlib

noncomputable section

namespace PI.Dv

section Abstract

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

structure GoodSet (K : Type) [Field K] (G : Type) [Group G] where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  W : S → Type
  [acgW : ∀ s, AddCommGroup (W s)]
  [modW : ∀ s, Module K (W s)]
  [fdW : ∀ s, FiniteDimensional K (W s)]
  [ntW : ∀ s, Nontrivial (W s)]
  tau : ∀ s, Representation K G (W s)

  irr : ∀ s, Function.Surjective (tau s).asAlgebraHom

  inj : Function.Injective fun s g => LinearMap.trace K (W s) (tau s g)

attribute [instance] GoodSet.finS GoodSet.decS GoodSet.acgW GoodSet.modW GoodSet.fdW GoodSet.ntW

structure Pair (K : Type) [Field K] (G : Type) [Group G] where
  H : Subgroup G
  chi : H →* Kˣ

def eS (T : GoodSet K G) (s : T.S) : MonoidAlgebra K G :=
  ∑ x : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)) • MonoidAlgebra.of K G x

def eG (T : GoodSet K G) : MonoidAlgebra K G := ∑ s, eS T s

end Abstract

section Lemma8

structure GMap (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G)
    (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE) where
  VK : Type
  [acgK : AddCommGroup VK]
  [modK : Module K VK]
  [fdK : FiniteDimensional K VK]
  rhoK : Representation K G VK
  V : Type
  [acgV : AddCommGroup V]
  [modV : Module ℂ V]
  rho : Representation ℂ G V

  j : VK →ₛₗ[σ] V
  j_indep : ∀ (n : ℕ) (b : Fin n → VK), LinearIndependent K b → LinearIndependent ℂ (fun i => j (b i))
  j_span : Submodule.span ℂ (Set.range j) = ⊤
  j_eq : ∀ g x, j (rhoK g x) = rho g (j x)

  good : rhoK.asAlgebraHom (eG T) = 1
  io : V →ₗ[ℂ] EE
  io_eq : ∀ g x, io (rho g x) = ρE g (io x)

attribute [instance] GMap.acgK GMap.modK GMap.fdK GMap.acgV GMap.modV

namespace GMap

end GMap

end Lemma8

end PI.Dv
