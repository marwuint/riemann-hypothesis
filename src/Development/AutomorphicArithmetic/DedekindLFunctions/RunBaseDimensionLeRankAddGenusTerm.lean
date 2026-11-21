import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace Deduction

structure PC where
  N : ℕ
  [nz : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

attribute [instance] PC.nz

namespace PC

def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PC :=
  @PC.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

def one : PC := PC.of (1 : DirichletCharacter ℂ 1)

def L (ψ : PC) (s : ℂ) : ℂ := DirichletCharacter.LFunction ψ.χ s

def kappa (ψ : PC) : ℂ := deriv (DirichletCharacter.LFunction ψ.χ) 1 / DirichletCharacter.LFunction ψ.χ 1

end PC

structure BFrame where
  G : Type
  [grp : CommGroup G]
  [fin : Fintype G]
  N : ℕ
  [nz : NeZero N]
  art : (ZMod N)ˣ →* G
  art_surj : Function.Surjective art
  d : ℕ
  d_prime : d.Prime
  d_mod : d % 4 = 3
  d_dvd : d ∣ N
  ch : G →* ℂˣ
  ch_art : ∀ u : (ZMod N)ˣ, ((ch (art u) : ℂˣ) : ℂ) = (jacobiSym (((u : ZMod N).val : ℕ) : ℤ) d : ℤ)
  iod : G
  inertia_d : ∀ g : G, (∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[d] N] ∧ art u = g) ↔ (g = 1 ∨ g = iod)
  ps : G →* ℂˣ
  ps_sq : ps ^ 2 = 1
  ps_conj : ps (art (-1)) = -1
  ps_iod : ps iod = 1
  A0 : Subgroup G
  base_exponent_le_a : A0 ≤ ch.ker ⊓ ps.ker
  split_ram : ∀ l : ℕ, l.Prime → l ≠ d →
    (∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] ∧ art u ≠ 1) → jacobiSym (l : ℤ) d = 1

attribute [instance] BFrame.grp BFrame.fin BFrame.nz

namespace BFrame

open Classical

variable (F : BFrame)

abbrev Char : Type := F.G →* ℂˣ

instance : Fintype F.Char := by
  haveI : NeZero ((Monoid.exponent F.G : ℕ) : ℂ) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  exact Fintype.ofFinite _

def c : F.G := F.art (-1)

def sg : F.G := F.c * F.iod

def Phi : Finset F.G := Finset.univ.filter fun g => F.ch g = 1

def A : Subgroup F.G := F.ch.ker ⊓ F.ps.ker

def f : ℕ := F.Phi.card

def n0 : ℕ := Nat.card F.A0

def o : ℕ := F.A0.relIndex F.A

def dir (θ : F.Char) : DirichletCharacter ℂ F.N := MulChar.ofUnitHom (θ.comp F.art)

def prim (θ : F.Char) : PC := PC.of (F.dir θ)

def Xp : Finset F.Char := Finset.univ.filter fun θ => (∀ s ∈ F.A0, θ s = 1) ∧ θ F.iod = 1

def Xm : Finset F.Char := Finset.univ.filter fun θ => (∀ s ∈ F.A0, θ s = 1) ∧ θ F.iod = -1

def bounded (S : Finset PC) : Finset F.Char := F.Xp.filter (fun θ => F.prim θ ∉ S) ∪ F.Xm

end BFrame

structure DType where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  J : ℝ
  one_le_J : 1 ≤ J
  KEPT : Finset PC
  one_mem : PC.one ∈ KEPT
  psK : Option PC
  oB : ℕ
  aStar : ℝ
  aStar_pos : 0 < aStar
  aStar_le : aStar ≤ 1
  cA : ℝ
  cA_pos : 0 < cA
  CB : ℝ
  kaN : ℝ
  kaN_nonneg : 0 ≤ kaN

namespace DType

end DType

open Classical in

structure Rows (T : DType) (x : ℝ) (F : BFrame) (n : ℕ) where
  m : ℕ
  k : ℝ
  m_ge : x ^ (1 / 2 - T.eps / 8) ≤ m
  m_le : (m : ℝ) ≤ x ^ (1 / 2 : ℝ)
  k_ge : x ^ (9 / 2 + 10 * T.eps) ≤ k
  k_le : k ≤ 2 * x ^ (9 / 2 + 10 * T.eps)
  TT : Finset F.G
  TT_sub : ∀ t ∈ TT, t ∈ F.A
  TT_ge : (Nat.card F.A : ℝ) * x ^ (-(T.eps / 8)) / 2 ≤ TT.card
  TT_share : ∀ g ∈ F.A, |((TT.filter fun t => g⁻¹ * t ∈ F.A0).card : ℝ) / TT.card -
    ((1 - T.aStar) / F.o + if g ∈ F.A0 then T.aStar else 0)| ≤ x ^ (-1 + T.eps)
  T2 : Finset F.G
  T2_subset_A0 : ∀ s ∈ T2, s ∈ F.A0
  T2_card_lower_bound : x ^ (-T.eps) ≤ (T2.card : ℝ) / F.n0
  aT : F.G → ℝ
  aT_ge : ∀ t ∈ TT, (x - 1) * Real.exp (x ^ T.eps) ≤ aT t
  aT_le : ∀ t ∈ TT, aT t ≤ (x + 1) * Real.exp (x ^ T.eps)
  om : ℝ
  om_le : 4 * F.f * x * om ≤ Real.exp (x ^ T.eps) / x
  w : F.G → Fin m → F.G → ℝ
  w_thick : ∀ u ∈ F.A0, ∀ j, ∀ s ∈ T2,
    Real.exp (x ^ T.eps) ≤ w u j (F.sg * u * s) ∧ w u j (F.sg * u * s) ≤ Real.exp (x ^ T.eps) + om
  w_thin : ∀ u ∈ F.A0, ∀ j, ∀ ρ ∈ F.Phi, (¬ ∃ s ∈ T2, ρ = F.sg * u * s) →
    0 < w u j ρ ∧ w u j ρ ≤ 2 * (x * Real.exp (x ^ T.eps) / Real.exp (x ^ (T.eps / 3)))
  Nc : ℝ
  Nc_le : Nc ≤ T.kaN * ((T2.card : ℝ) / F.n0) * k * Real.exp (x ^ T.eps) * x ^ (2 * T.eps) / n

namespace Rows

end Rows

end Deduction

end
