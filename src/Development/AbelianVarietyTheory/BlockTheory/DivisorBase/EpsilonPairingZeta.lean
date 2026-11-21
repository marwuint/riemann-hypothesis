import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

open GlobalTheory.PDivGroup GlobalTheory.Sandwich

structure IsIntegers (O C : Type) [CommRing O] [NormedField C] [Algebra O C] : Prop where

  inj : Function.Injective (algebraMap O C)

  mem_iff : ∀ x : C, (∃ a : O, algebraMap O C a = x) ↔ ‖x‖ ≤ 1

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

def zeta (ε : PreTilt O p) (n : ℕ) : O := PreTilt.untilt (root^[n] ε)

theorem zeta_succ_pow (ε : PreTilt O p) (n : ℕ) : zeta ε (n + 1) ^ p = zeta ε n := by
  unfold zeta
  rw [← map_pow, Function.iterate_succ_apply']
  congr 1
  exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply _

def IsPrimitiveSystem (ε : PreTilt O p) : Prop := ∀ n, IsPrimitiveRoot (zeta ε n) (p ^ n)

theorem IsPrimitiveSystem.zeta_zero {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    zeta ε 0 = 1 := by simpa using (hε 0).pow_eq_one

def epsTate {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : (PDivGroup.mu p O).Tate :=
  muTate O (zeta ε) hε.zeta_zero (zeta_succ_pow ε)

def epsEquiv [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    ℤ_[p] ≃ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ (epsTate hε))
    (smul_muTate_bijective (zeta ε) hε.zeta_zero (zeta_succ_pow ε) hε)

def epsPairing [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (t : G.Tate) (χ : G.dual.Tate) : ℤ_[p] :=
  (epsEquiv hε).symm (pairing G O t χ)

theorem epsPairing_smul [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε)
    (G : PDivGroup p O) (t : G.Tate) (χ : G.dual.Tate) :
    epsPairing hε G t χ • epsTate hε = pairing G O t χ :=
  (epsEquiv hε).apply_symm_apply _

def toO {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (t : G.Tate) :
    Fin h → O := fun i => padicToO p O (e t i)

def pairingO [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) {G : PDivGroup p O}
    {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (y : Fin h → O) (χ : G.dual.Tate) : O :=
  ∑ i, y i * padicToO p O (epsPairing hε G (e.symm (Pi.single i 1)) χ)

theorem pairingO_toO [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε)
    {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (t : G.Tate)
    (χ : G.dual.Tate) : pairingO hε e (toO e t) χ = padicToO p O (epsPairing hε G t χ) := by
  have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
    apply e.injective
    rw [map_sum]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [ht]
  simp only [pairingO, toO, epsPairing, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, map_mul]

section Datum

variable {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def actH (D : Datum ε h Λ) (a : Λ) : (Fin h → O) →ₗ[O] (Fin h → O) :=
  Matrix.toLin' ((D.ρM a).map (fontaineTheta O p))

def bQuot (D : Datum ε h Λ) : ((Fin h → O) ⧸ D.Fil) →ₗ[O] (Fin h → O) :=
  D.Fil.liftQ D.bb le_rfl

structure Realizes [IsDomain O] (hε : IsPrimitiveSystem ε) (u₁ u₂ : Oˣ) (G : PDivGroup p O)
    (ρ : Action Λ G) (D : Datum ε h Λ) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie) : Prop where

  tate_act : ∀ (a : Λ) (t : G.Tate), e (ρ.onTate O a t) = D.ρT a *ᵥ e t

  fil_act : ∀ (a : Λ) (w : G.dual.omega),
    (fil (ρ.onOmegaDual a w) : Fin h → O) = actH D a (fil w)

  lie_act : ∀ (a : Λ) (m : Fin h → O),
    lie (D.Fil.mkQ (actH D a m)) = ρ.onLie a (lie (D.Fil.mkQ m))

  al_eq : ∀ t : G.Tate, D.al (toO e t) =
    (u₁ : O) • (fil (omegaMap G.dual (PDivGroup.mu p O) (dualChar G t) (dlogT p O)) : Fin h → O)

  b_eq : ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ =
    (u₂ : O) * x (omegaMap G (PDivGroup.mu p O) (charHom G χ) (dlogT p O))

end Datum

def HodgeTateSandwichAt [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : Prop :=
  ∃ u₁ u₂ : Oˣ, ∀ (G : PDivGroup p O) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ρ : Action Λ G),
    ∃ (D : Datum ε G.height Λ) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]))
      (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin G.height → O) ⧸ D.Fil) ≃ₗ[O] G.Lie),
      Realizes hε u₁ u₂ G ρ D e fil lie

section Inhabitant

variable [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε)

omit [IsDomain O] in
theorem mult_bb (y : Fin 1 → O) : (mult ε).bb y = y := by
  simp [Datum.bb, mult]

omit [IsDomain O] in
theorem mult_Fil : (mult ε).Fil = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun y hy => (mult_bb y).symm.trans hy

omit [IsDomain O] in
instance : Subsingleton (mult ε).Fil := by rw [mult_Fil]; infer_instance

end Inhabitant

end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta
