import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace Formalism.L2.Ker.I3.JetMomA

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def vecZ (D : D7) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (q n : ℕ) [Fact q.Prime]
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[q]) : VC D N N' :=
  δ • embV D T (∑ i, (((PadicInt.toZModPow n (a i)).val : ℕ) : D.host.E) • b i)

abbrev Meas (q r : ℕ) [Fact q.Prime] : Type := C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]

section Stmts

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ) (q : ℕ) [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q])

def IntSplit : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' →
    ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[q], IsComb D B.tor (B.eNat χ) lam L L' F →
      (∀ (C : WeierstrassCurve.VariableChange ℂ_[q]) (wq : PowerSeries ℂ_[q]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam B.tor.abelian₂ C → IsWq (C • wModel lam B.tor.abelian₂) wq → LocBasis D q (YYl D L L') b →
        IntegralMv (atLog D lam B.tor.abelian₂ C wq b F)) ∧
      JetsInt D lam (YYl D L L') F

variable {D cc δ q} (Ω : ℂ_[q]) {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
  (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)

def TranslateJetMomentLaw : Prop :=
  ∀ (n : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam (2 * n + 2) ε → ∀ yt : Fin r → Fin (q ^ n),
    ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (kap D B.tor (vecZ D B.tor δ q n b a) (liftY D B.tor δ q n ε b yt)) *
        ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (Wop D B.tor q (liftY D B.tor δ q n ε b yt) (B.eNat χ N N' L L'))) = μ g

variable (D cc δ q)

end Stmts

end Formalism.L2.Ker.I3.JetMomA
