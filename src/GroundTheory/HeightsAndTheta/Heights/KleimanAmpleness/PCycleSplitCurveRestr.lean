import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMemSupport

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace CycleSplit.Curve.Restr

section H0

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R]
  {G : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type*} [AddCommGroup M] [Module R M] (π : ∀ I : Cell U, M →ₗ[R] G I)

def constK : M →ₗ[R] Cech.Cochain G 0 where
  toFun m K := π K.1 m
  map_add' a b := funext fun K => map_add (π K.1) a b
  map_smul' c a := funext fun K => map_smul (π K.1) c a

variable (hπ : ∀ I J h m, ρ I J h (π I m) = π J m)

include hπ in
theorem constK_cocycle (m : M) : Cech.d G ρ 0 (constK π m) = 0 :=
  Cech.d_zero_of_compat (v := fun I => π I m) (fun I J h => hπ I J h m)

def toH0 : M →ₗ[R] Cech.H G ρ 0 :=
  (Submodule.mkQ _).comp ((constK π).codRestrict (LinearMap.ker (Cech.d G ρ 0))
    fun m => LinearMap.mem_ker.mpr (constK_cocycle π hπ m))

end H0

section Quot

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

end Quot

end CycleSplit.Curve.Restr

end

end GroundTheory.Heights₂.Heights.Kleiman
