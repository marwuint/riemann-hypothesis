import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSqNonsplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitTw

variable {D : D7}

set_option maxHeartbeats 2000000 in

def twFL (L : LocAll (lay0 D)) (F : TwFrameC D) : TwFrameC (withLoc L) := { F with }

set_option maxHeartbeats 4000000 in
theorem twTiedL (L : LocAll (lay0 D)) {F : TwFrameC D} {low : Finset ℕ} (h : TwistFrameLowIndexCompatibility D F low) :
    TwistFrameLowIndexCompatibility (withLoc L) (twFL L F) low := { h with }

set_option maxHeartbeats 4000000 in
theorem choiceL (L : LocAll (lay0 D)) {C : NChoice D} (h : ChoiceC D C) : ChoiceC (withLoc L) (chL L C) := { h with }

set_option maxHeartbeats 20000000 in

def mtVL (L : LocAll (lay0 D)) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [g : AddCommGroup W₀]
    [m : Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (V : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) : @NX.MtVReal (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ :=
  @NX.MtVReal.mk (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ V.W V.acg V.mod V.fd V.ρ V.irr V.alg V.bc V.J V.χ V.J_open V.hyp V.QP V.QP_sub V.QP_cover V.QP_nconj V.DP V.DP_sub V.DP_cover V.DP_nconj V.sp V.sp_w V.redG V.J_mem V.chi_eq V.real

set_option maxHeartbeats 4000000 in

def expL (L : LocAll (lay0 D)) (X : NExpTied D) : NExpTied (withLoc L) :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      (@mtVL D L i j b k Q ψ X.sgnT (X.Wt i j b) (X.acgWt i j b) (X.modWt i j b) (X.rhoW i j b) (X.tauG i j b) (X.mtV i j b k Q ψ h1 h2 h)) }

set_option maxHeartbeats 4000000 in
theorem nctL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) (h : NChTie D C) : NChTie (withLoc L) (chL L C) where
  twOf_eq := Sp.twOf_eq
  twSide_eq := Sp.twSide_eq
  Q_eq a := (Sp.Q_eq _ _ a ((L.X.locs_mem _ _ a).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  psi_eq := by
    obtain ⟨ψ0, h1, h2, -⟩ := h.psi_eq
    exact ⟨ψ0, h1, h2, fun a g => Sp.psi_eq a g _ (h2 _ g)⟩
  embedding_baseField_condition := h.embedding_baseField_condition

set_option maxHeartbeats 4000000 in
theorem chSideL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) {cf : CharFrame D} {X : NExpTied D} {tp : TupTied D cf C}
    (h : ChoiceSide D cf M X C tp) : ChoiceSide (withLoc L) (cfL L cf) (mtL L M) (expL L X) (chL L C) (tpL L tp) where
  nct := nctL Sp h.nct
  choice := choiceL L h.choice
  off := h.off
  adm := h.adm
  psi := h.psi
  eMt_level := h.eMt_level

set_option maxHeartbeats 4000000 in

def chiDL (L : LocAll (lay0 D)) (K : NC.NChiData D) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E) : NC.NChiData (withLoc L) :=
  { K with psi := ψ }

set_option maxHeartbeats 4000000 in
theorem chiL (L : LocAll (lay0 D)) {K : NC.NChiData D} (h : NC.NormalizedCharacterCompatibility D K) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) :
    NC.NormalizedCharacterCompatibility (withLoc L) (chiDL L K ψ) :=
  { h with psi := hψ }

set_option maxHeartbeats 4000000 in
theorem deltaReadL (L : LocAll (lay0 D)) {cf : CharFrame D} (h : DeltaRead D cf) : DeltaRead (withLoc L) (cfL L cf) := h

end GlobalTheory.HeightCounting.FitTw

end
