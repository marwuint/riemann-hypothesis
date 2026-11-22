import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O

namespace GlobalTheory.MixedLocalChains

structure Term {D : D7} (Y : ShimX D.what₂.Tau) (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (w : ι → ℝ)
    (jc : ι → (KW p →+* ℂ)) (M : ∀ la, DV.Mdl D p Y.N (rkOf (PsiOf D (jc la)) Y.N Y.j))
    (rt : ∀ la, Bool × Rt D.what₂.Tau Y.N → (M la).Z.LB) : Prop where
  sum_w : ∑ la, w la = 1
  lie : ∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : ι → Emb D p), (∀ la, (jc la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (rkOf (PsiOf D (jc la)) Y.N Y.j (τ' la))) (i' : Fin Y.N), (∀ la, (i' : ℕ) = i la) →
    ∀ G : MvPolynomial (Vm D.what₂.Tau Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) (dimFl D.what₂.Tau Y.N) →
      Y.arMix Sx R p (dRt D.what₂.Tau Y.N (τ0, i') * toR G) = Real.log p * ∑ la, w la *
        ((((M la).Z.capDeg (((M la).lie (τ' la)).Dv (i la)) (evC (M la) (rt la) G) : ℚ) : ℝ) / ((M la).cov : ℝ))
  om : ∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : ι → Emb D p), (∀ la, (jc la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (Y.N - rkOf (PsiOf D (jc la)) Y.N Y.j (τ' la))) (i' : Fin Y.N), (∀ la, (i' : ℕ) = Y.j + i la) →
    ∀ G : MvPolynomial (Vm D.what₂.Tau Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) (dimFl D.what₂.Tau Y.N) →
      Y.arMix Sx R p (dRt D.what₂.Tau Y.N (τ0, i') * toR G) = Real.log p * ∑ la, w la *
        ((((M la).Z.capDeg (((M la).om (τ' la)).Dv (i la)) (evC (M la) (rt la) G) : ℚ) : ℝ) / ((M la).cov : ℝ))

section Pairs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O}

variable (B) in

structure Pres where
  r : ℕ
  E : B.X.Modules
  E' : B.X.Modules
  vb : GlobalTheory.VB.IsVB E r
  vb' : GlobalTheory.VB.IsVB E' r
  ψ : E' ⟶ E
  iso : IsIso (B.genRes.map ψ)

def Pres.mod (P : Pres B) : B.X.Modules := cokernel P.ψ

def Kills (g : Γ(B.X, ⊤)) (F : B.X.Modules) : Prop := smulHom F g = 0

def IsRootOfP (g : Γ(B.X, ⊤)) (a : ℕ) : Prop := ∃ u : Γ(B.X, ⊤)ˣ, g ^ a = u * (p : Γ(B.X, ⊤))

variable (B) in

def fibI : B.X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {(p : Γ(B.X, ⊤))})

def IsFrob (F F' : B.X.Modules) : Prop := ∃ h : (p : Γ((fibI p B).subscheme, ⊤)) = 0,
  Nonempty (F' ≅ (Scheme.Modules.pushforward (fibI p B).subschemeι).obj ((Scheme.Modules.pullback
    (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h ≫ (fibI p B).subschemeι)).obj F))

def IsExt (F₁ F₂ F₃ : B.X.Modules) : Prop := ∃ S : ShortComplex B.X.Modules, S.ShortExact ∧
  Nonempty (S.X₁ ≅ F₁) ∧ Nonempty (S.X₂ ≅ F₂) ∧ Nonempty (S.X₃ ≅ F₃)

variable (B) in

structure Chain {ι : Type} (φ : ι → ι) (o : ℕ) where
  π : Γ(B.X, ⊤)
  g : Γ(B.X, ⊤)
  π_root : IsRootOfP p π (p - 1)
  g_root : IsRootOfP p g p
  lw : ι → Pres B
  wl : ∀ τ, (lw τ).E ⟶ (lw τ).E'
  lw_wl : ∀ τ, (lw τ).ψ ≫ wl τ = smulHom _ π
  oo : ι → Pres B
  q : ℕ → ι → Pres B
  l : ℕ → ℕ → ι → Pres B
  c3 : ∀ τ, IsExt (cokernel (wl τ)) (q 0 τ).mod (oo τ).mod
  step : ∀ n < o, ∀ τ, IsExt (q (n + 1) τ).mod (q n τ).mod (l n 0 τ).mod
  l_frob : ∀ n < o, ∀ i ≤ n, ∀ τ, Kills g (l n i τ).mod ∧ IsFrob p (l n i τ).mod (l n (i + 1) τ).mod
  l_last : ∀ n < o, ∀ τ, Nonempty ((l n (n + 1) τ).mod ≅ cokernel (smulHom (lw (φ^[n + 1] τ)).E' (p : Γ(B.X, ⊤))))
  q_frob : ∀ n < o, ∀ τ, Kills g (q (n + 1) τ).mod ∧ IsFrob p (q (n + 1) τ).mod (q n (φ τ)).mod

end Pairs

end GlobalTheory.MixedLocalChains

end
