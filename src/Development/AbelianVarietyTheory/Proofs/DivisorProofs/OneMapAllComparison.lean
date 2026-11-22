import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.OneMapAllCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory CategoryTheory.Hom.group in
theorem levR_congr (c : Coeff l) (hA : l.A = 1) {p q : (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ a, p.1 a - q.1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR p y y' ↔ levR q y y' := by
  have e : ∀ a, Xo.univ.eta (p.1 a) = Xo.univ.eta (q.1 a) := fun a => by
    rw [← sub_add_cancel (p.1 a) (q.1 a), Xo.univ.eta_add, Xo.univ.eta_ker _ (h a), one_mul]
  have e1 : ∀ a, Xo.univ.etaA a = 1 := fun a => by
    have := Xo.univ.etaA_ker a
    rwa [hA, one_smul] at this
  unfold levR IsLevMove
  simp only [e, e1]

variable {G : Type} [Group G] {lev lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem rel_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g y y') =
      fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev' g y y' := by
  funext S _ _ g y y'
  exact propext (levR_congr c hA (h g) y y')

theorem actLev_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    actLev (Xo := Xo) c lev = actLev c lev' := by
  funext g
  unfold actLev
  rw [rel_congr c hA h]

theorem second_level_eq_one {c : Coeff l} {n : ℕ} {Tup : Type} {dδ : Tup → DeltaDat Xo c n} (h : CovPin Xo c dδ) (t : Tup) :
    l.A = 1 := by
  have h1 := (h t).1.1.2.2
  rw [(h t).2.1] at h1
  exact Nat.dvd_one.1 h1

end Level

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def phi0 (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ)
    (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) T.toCore.σ₀))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) T.toCore.σ₀)) (castDict hV (T.mu ((i : ℕ) + 1) T.toCore.σ₀)) cc)
    (rdU (T.U ((i : ℕ) + 1) T.toCore.σ₀) f)

def PhaseRational (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i)
    (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) : Prop :=
  ∀ x : A.fam.amb.FL i A.μ0, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n), ∀ h,
    ph * (R.HW i (sg0 D A)).e (R.thG i A.μ0 (jVx R i A.μ0 x)) (v₀ i (sg0 D A)) h =
      ∑ k, D.what₂.embLL (a k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        phi0 T i hV cc (f k : T.R ((i : ℕ) + 1)) h)

variable {T R} in

theorem phRat_iff {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i) (cc : (T.U ((i : ℕ) + 1) T.toCore.σ₀).Comp → ℂ) (ph : ℂ) :
    O.PhRat (κ i) (v₀ i (sg0 D A)) cc ph ↔ PhaseRational T R κ v₀ i hV cc ph := Iff.rfl

def LevUnique (i : Fin D.R.m) : Prop :=
  ∀ lev lev' : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev' →
      ∀ g a, lev g a - lev' g a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La)

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

variable {T R κ v₀ O ph}

variable (T R κ v₀ O ph)

end GlobalTheory.OneMapAllCompare
