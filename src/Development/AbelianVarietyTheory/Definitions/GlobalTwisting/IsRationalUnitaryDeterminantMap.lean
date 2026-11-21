import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CcKPrimitive

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.GH

variable {e : ℕ} (H : GHost e)

instance psiFintype : Fintype H.Psi := Fintype.ofFinite _

def OverP (p : ℕ) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal

def embPsi (g : H.Psi) : H.E →+* ℂ := H.emb (g : H.GG)

def IsConjPl (w w' : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → (x ∈ w.asIdeal ↔ y ∈ w'.asIdeal)

def IsSplitPl (v : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  ∃ x : 𝓞 H.E, x ∈ v.asIdeal ∧ ∀ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y ∉ v.asIdeal

structure IsClsF (ξ : HChar H.E) : Prop where
  unitary : ξ.IsUnitary
  unr : ∀ v, ξ.UnrAt v
  inf : ∀ k, ξ.inf k = 1
  triv : ξ.TrivOn H.F

structure IsEtaT (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  res : χ.ResEta H.F
  inf : χ.HasInf (embPsi H) (fun _ => 1)

structure IsChiPsi (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  triv : χ.TrivOn H.F
  inf : χ.HasInf (embPsi H) (fun _ => 2)

structure PiBar where
  pb : Fin 2 → HeightOneSpectrum (𝓞 H.K)
  pb_over : ∀ k, ((H.g k : ℕ) : 𝓞 H.K) ∈ (pb k).asIdeal

def PiBar.Div {H : GHost e} (P : PiBar H) (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  w.under (𝓞 H.K) = P.pb k

structure Omg where
  om : ∀ k : Fin 2, (ZMod (H.g k))ˣ →* ℂˣ
  gen : ∀ k, Function.Injective (om k)

variable {H}

structure IsMu0 (P : PiBar H) (W : Omg H) (a : H.Psi → ℚ) (j : ℕ) (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  triv : χ.TrivOn H.F
  inf : χ.HasInfQ (embPsi H) (fun τ => -a τ)
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v
  tame : ∀ v, χ.TameAt v
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (b : ℕ) (hb : b.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (b : H.E) → χ.locK w x = (W.om k (ZMod.unitOfCoprime b hb) ^ (2 * (j + 1)))⁻¹

structure IsDelta (p : ℕ) (χ : HChar H.E) : Prop where
  fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  unr : ∀ v, ¬ OverP H p v → χ.UnrAt v
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → χ.loc v x ^ n = 1) ↔ 15 ∣ n

structure IsPsi (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (χ : HChar H.E) : Prop where
  ord : ∃ a : ℕ, χ.OrderDvd (l ^ a)
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  ram : ∀ v, χ.UnrAt v ↔ v ∉ Q
  atl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1
  split : ∀ v ∈ Q, IsSplitPl H v

variable (H)

structure HFrame {m : ℕ} (a : Fin m → H.Psi → ℚ) where
  P : PiBar H
  W : Omg H
  mu0 : Fin m → HChar H.E
  eta : HChar H.E
  chiPsi : HChar H.E
  del : HChar H.E
  del' : HChar H.E
  isMu0 : ∀ j, IsMu0 P W (a j) j.1 (mu0 j)
  isEta : IsEtaT H eta
  isChi : IsChiPsi H chiPsi
  isDel : IsDelta (H := H) H.pde del
  isDel' : IsDelta (H := H) H.pde' del'

end GlobalTheory.GH
