import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.Divisibility.Numbers

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open Formalism.LatticeIndexTer (ph)

def kernelBound_sq (N : NumDatum) (δ : Code N) (T : ℕ) (CK : ℝ) (j : ℕ) (logOm : RPl N.R → ℝ) (logTh : ℝ)
    (h h' n n' : ℕ) : ℝ :=
  (∑ z : RPl N.R, ((∑ i ∈ Finset.range (N.R.N (j - 1)), ph ((N.nu δ j z i : ℚ) : ℝ)) - ((N.nuAbs δ j z : ℚ) : ℝ) * logOm z)) +
    logTh +
    ((N.R.f : ℝ) * ((N.R.N (j - 1) : ℝ) * N.R.N j) * Real.log (8 + 32 * ((N.R.f : ℝ) * ((N.R.N (j - 1) : ℝ) * N.R.N j)) * N.v) +
      2 * (CK * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T)) +
      (∑ z : RPl N.R, (1 + 2 * ((N.R.N (j - 1) : ℝ) * N.R.N j) * Real.log (2 * ((N.nuAbs δ j z : ℚ) : ℝ) + 2))) +
      Real.log ((h : ℝ) * h')) +
    Real.log ((n : ℝ) * n')

def IsTopPl (N : NumDatum) (z : RPl N.R) : Prop := z.1 = false ∧ z.2 ∈ N.TT

section Arch

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {dl : ℂ} (B : Base D cc dl) (cD : D.what₂.Tau → ℂ)

def logOmAt (_B : Base D cc dl) (cD : D.what₂.Tau → ℂ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (τ : D.what₂.Tau) : ℝ :=
  -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))

def logThAt (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (a b : ℕ) : ℝ :=
  Real.log (TaylorLogMetric.normSq D (TaylorLogMetric.torConj D B.tor M ρ)
    (TaylorLogMetric.La D (TaylorLogMetric.torConj D B.tor M ρ) (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b)) (TaylorLogMetric.fnConj D M ρ (B.thZero a b)))

def ThetaFieldData {K : Type} [Field K] (σ₀ : K →+* ℂ) (R : Ranks) (M : IntermediateField ℚ ℂ) : Prop :=
  (∀ k, σ₀ k ∈ M) ∧ TaylorLogMetric.DataIn D B.tor M ∧ (∀ τ, cD τ ∈ M) ∧
    ∀ i < R.m, TaylorLogMetric.CoefIn D (B.thZero (R.N i) (R.N (i + 1))) M

end Arch

def placeUnder {K : Type} [Field K] (σ₀ : K →+* ℂ) {M : IntermediateField ℚ ℂ} (h : ∀ k, σ₀ k ∈ M) (ρ : M →ₐ[ℚ] ℂ) :
    InfinitePlace K :=
  InfinitePlace.mk ((ρ : M →+* ℂ).comp (σ₀.codRestrict M h))

open Classical in

def JetsInField {X : Fields} (A : Amb X) (a b : ℕ) (Sb : Finset (HeightOneSpectrum (𝓞 X.E))) (Md : ℕ) (deg : X.Tau → ℤ) : Prop :=
  ∀ (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange Sb Md c L L' x → ∀ e : DVar X.Tau a b →₀ ℕ,
      (∀ τ, ((∑ k ∈ e.support.filter (fun k => k.1 = τ), e k : ℕ) : ℤ) = deg τ) →
      ∃ y : X.K, A.σ₀ y = (A.chiF a b L L')⁻¹ * jetC A.cD (A.thInd Sb L L' c x) e

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg)
  (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)

def topClassNumber : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient
    ((⊤ : Subgroup (UF X.E (R.N R.m))).prod
      (((rowTy Ch sel mu (rPsymF Ch)).grp).map (extGH (SG := rowSG Pr sel mu) (N_m_succ R))))
    (DecoSet X.E (R.N R.m) (Pr.vT u) (rowSG Pr sel mu)))

def classNumberAt (j : ℕ) : ℕ :=
  if j = R.m then topClassNumber Ch sel mu u
  else Finset.univ.sup fun b : I.β j => Nat.card ((chF W sel mu I u j).mem b).Cl

def indexCount (j : ℕ) : ℕ :=
  if j = R.m then 1
  else if j + 1 = R.m then (ybSet sel mu cst (Formalism.L2.Col.stdLat X.E (R.N j))).ncard
  else Fintype.card (I.β j)

def FieldOfDefinition (A : Amb X) : Prop :=
  ∀ i < R.m, JetsInField A (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
    (fun τ => ∑ a, (W.nuW u (i + 1) τ).w a)

end Chain

def StepBound_sq {K : Type} [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t : ℝ) : Prop :=
  ∀ φ : (Q.F i).Forms, (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤
    Real.exp t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re

def CplBound_sq {K : Type} [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t : ℝ) : Prop :=
  ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤
    Real.exp t * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re

section Ties

variable {D : D7} (N : NumDatum) {X : Fields} (s : Seam D X) (Pr : Primes X)

def HostTie : Prop :=
  D.R = N.R ∧ N.q = D.host.q ∧ N.d = D.host.d ∧ D.host.ccK = ⊤ ∧ GL3Theta.InducedCMType D ∧ GL3Theta.HostFieldConditions D ∧
    X.AbelianUnramifiedExtensionConditions ∧ s.Ok ∧ (∀ x : X.K, s.σ₀ (star x) = starRingEnd ℂ (s.σ₀ x)) ∧
    Pr.Ok ∧ Pr.PiGCong ∧ Pr.cond = N.cond ∧ (∀ i, Pr.g i = N.g i) ∧ (∀ i, D.host.g i = N.g i) ∧
    HEq N.H D.host.toHostAx

variable {N s Pr} in

theorem HostTie.host_heq (h : HostTie N s Pr) : HEq N.H D.host.toHostAx := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2

variable {N s Pr} in

theorem HostTie.rd_eq (h : HostTie N s Pr) : N.rd = D.host.rdE := by
  have hH := h.host_heq
  have hR := h.1
  obtain ⟨R, sc, H, g, gp, TT, Del, h0, hc⟩ := N
  dsimp only at hR hH
  subst hR
  obtain rfl := eq_of_heq hH
  rfl

variable {N s Pr} in

theorem HostTie.cond_eq (h : HostTie N s Pr) : N.cond = D.host.condN := by
  have hH := h.host_heq
  have hR := h.1
  obtain ⟨R, sc, H, g, gp, TT, Del, h0, hc⟩ := N
  dsimp only at hR hH
  subst hR
  obtain rfl := eq_of_heq hH
  rfl

variable {N s Pr} in

theorem HostTie.pr_cond (h : HostTie N s Pr) : Pr.cond = D.host.condN :=
  h.2.2.2.2.2.2.2.2.2.2.2.1.trans h.cond_eq

variable {Pr}

def WeightTie (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) : Prop :=
  W.Ok ∧ (∀ z, pl z ∈ W.tops ↔ IsTopPl N z) ∧
    ∀ z, RowPar.of (W.hc u (pl z)) = RowPar.of (N.hc z) ∧ ∀ i, (W.hc u (pl z)).u i = N.uW δ z i

def CharTie (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) : Prop :=
  Ch.Ok ∧ G.σ₀ = s.σ₀ ∧ s.iE G.xi0 = D.host.xi0 ∧
    (∃ eta : Formalism.L2.Host.HChar X.E, Ch.Tied s.σ₀ (fun j τ => (W.row τ).e j) G.mu0 eta) ∧
    Ch.WeilTied s.σ₀ G.xi0 ∧ IsSel X sel

end Ties

def AnalyticTie (D : D7) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK dl ∧ TaylorLogMetric.IsChi D χ ∧ IsDgen D cD

section Concl

variable {D : D7} (N : NumDatum) {X : Fields} (s : Seam D X) {Pr : Primes X} (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg)
  (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K)))
  {dl : ℂ} (B : Base D D.host.ccK dl) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N)

def liftBound_sq (CK : ℝ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (j : ℕ) : ℝ :=
  kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z))) (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j))
    (classNumberAt W Ch sel mu I u (j - 1)) (classNumberAt W Ch sel mu I u j)
    (indexCount sel mu cst I (j - 1)) (indexCount sel mu cst I j)

end Concl

theorem StepBound_sq.mono {K : Type} [Field K] [NumberField K] [StarRing K] {Q : KerChain K} {i : ℕ} {v : InfinitePlace K}
    {t t' : ℝ} (h : StepBound_sq Q i v t) (ht : t ≤ t') (hpos : ∀ φ, 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re) :
    StepBound_sq Q i v t' := fun φ =>
  (h φ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ht) (hpos φ))

end GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds
