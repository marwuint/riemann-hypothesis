import Mathlib
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.ColFormsLemmas

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

structure PlTie (X : Fields) (P : Places p O Kf) where
  pr : Fin P.nV → HeightOneSpectrum (𝓞 X.E)
  iw : ∀ v, X.E →+* P.Qq v
  eK : X.K →+* Kf
  pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ X.Tau
  pr_inj : Function.Injective pr
  pr_ne : ∀ v v', pr v ≠ conjPrime₂ (pr v')
  pr_all : ∀ Q : HeightOneSpectrum (𝓞 X.E), ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal ↔ ∃ v, Q = pr v ∨ Q = conjPrime₂ (pr v)
  iw_int : ∀ v x, IntAt (pr v) x ↔ iw v x ∈ Set.range (algebraMap (P.W v) (P.Qq v))
  iw_dense : ∀ v (y : P.W v) (n : ℕ), ∃ (x : 𝓞 X.E) (z : P.W v),
    iw v (x : X.E) = algebraMap (P.W v) (P.Qq v) (y + (p : P.W v) ^ n * z)
  even : ∀ v (s : Fin (P.n' v)), Even s.val → ∀ x, eK (X.emb (pos ⟨v, s⟩) x) = P.ι v ((P.σ v ^ s.val) (iw v x))
  odd : ∀ v (s : Fin (P.n' v)), ¬ Even s.val → ∀ x, eK (X.embBar (pos ⟨v, s⟩) x) = P.ι v ((P.σ v ^ s.val) (iw v x))

def SameOff {E : Type} [Field E] [NumberField E] {n : ℕ} (p : ℕ) (N N' : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal → localization₂ Q.asIdeal N = localization₂ Q.asIdeal N'

structure PSys (X : Fields) (n p : ℕ) (lam : X.Tau → DomWeight n) (S : GSD X.K) where
  u : S.G →* UF X.E n
  chr : S.G →* X.Kˣ
  eV : S.V ≃ₗ[X.K] VV X.K lam
  N : S.D → Submodule (𝓞 X.E) (Sp X.E n)

  Aw : S.D → S.D → Prop
  aw_equiv : Equivalence Aw
  aw_smul : ∀ (g : S.G) d d', Aw d d' → Aw (g • d) (g • d')
  aw_off : ∀ d d', Aw d d' → SameOff p (N d) (N d')
  aw_ex : ∀ d N', Submodule.IsLattice X.E N' → IsUnimodular (hStd X.E n) N' → SameOff p (N d) N' → ∃! d', Aw d d' ∧ N d' = N'
  lat : ∀ d, Submodule.IsLattice X.E (N d)
  uni : ∀ d, IsUnimodular (hStd X.E n) (N d)
  N_smul : ∀ (g : S.G) d, N (g • d) = gmap (u g).1 (N d)
  chr_root : ∀ g, ∃ k : ℕ, 0 < k ∧ chr g ^ k = 1
  rho : ∀ g x, eV (S.ρ g x) = ((chr g : X.Kˣ) : X.K) • rhoVr X.emb lam (ufGL X.E n (u g)) (eV x)
  del : ∀ d (w : HeightOneSpectrum (𝓞 X.K)), ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ x,
    x ∈ localization₂ w.asIdeal (S.Del d) ↔ eV x ∈ localization₂ w.asIdeal (delAtr X.emb lam (N d))
  nab : ∀ d (w : HeightOneSpectrum (𝓞 X.K)), ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ x,
    x ∈ localization₂ w.asIdeal (S.Nab d) ↔ eV x ∈ localization₂ w.asIdeal (nabAtr X.emb lam (N d))

section Loc

variable {X : Fields} {P : Places p O Kf} (T : PlTie X P) {n : ℕ} (hn : n = P.m + 1)

def PlTie.vec (v : Fin P.nV) (x : Sp X.E n) : Fin (P.m + 1) → P.Qq v := fun i => T.iw v (x (Fin.cast hn.symm i))

def PlTie.tup (N : Submodule (𝓞 X.E) (Sp X.E n)) : P.Tup := fun v => Submodule.span (P.W v) (T.vec hn v '' (N : Set (Sp X.E n)))

def PlTie.act (v : Fin P.nV) : UF X.E n →* GL (Fin (P.m + 1)) (P.Qq v) :=
  (Formalism.UG.bc (T.iw v)).comp
    ((Units.map (Matrix.reindexAlgEquiv X.E X.E (finCongr hn)).toMulEquiv.toMonoidHom).comp (ufGL X.E n))

def PlTie.detTw (c : ℤ) (γ : UF X.E n) : Kf :=
  (∏ τ, T.eK (X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))) ^ c

structure ValTie (lam : X.Tau → DomWeight n) (c : ℤ) where
  θ : VV X.K lam →ₛₗ[T.eK] P.Xsp
  li : LinearIndependent Kf fun i => θ (bVV X.K lam i)
  span : Submodule.span Kf (Set.range θ) = P.Vtup
  equiv : ∀ (γ : UF X.E n) x, θ (rhoVr X.emb lam (ufGL X.E n γ) x) = T.detTw c γ • P.natAct (fun v => T.act hn v γ) (θ x)
  del : ∀ N, Submodule.IsLattice X.E N → IsUnimodular (hStd X.E n) N →
    Submodule.span O (θ '' (delAtr X.emb lam N : Set (VV X.K lam))) = P.HtupW (T.tup hn N)
  nab : ∀ N, Submodule.IsLattice X.E N → IsUnimodular (hStd X.E n) N →
    Submodule.span O (θ '' (nabAtr X.emb lam N : Set (VV X.K lam))) = P.Htup (T.tup hn N)

end Loc

namespace RetractionModules

end RetractionModules

namespace PSys

end PSys

end GlobalTheory.GO
