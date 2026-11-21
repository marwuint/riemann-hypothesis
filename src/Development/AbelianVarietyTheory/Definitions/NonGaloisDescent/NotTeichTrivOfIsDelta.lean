import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedPowSubOneLtOne

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

namespace GlobalTheory.LamTie

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def TeichTriv (χ : Formalism.L2.Host.HChar H.E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 H.E), OverP H H.pde w ∨ OverP H H.pde' w →
    ∀ x : (w.adicCompletion H.E)ˣ, x ^ (Ideal.absNorm w.asIdeal - 1) = 1 → χ.loc w x = 1

variable {H} {χ χ' : Formalism.L2.Host.HChar H.E}

theorem isUnitAt_of_pow_eq_one {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {x : (w.adicCompletion E)ˣ}
    (hx : x ^ (Ideal.absNorm w.asIdeal - 1) = 1) : IsUnitAt w x := by
  have h1 : Ideal.absNorm w.asIdeal - 1 ≠ 0 := by have := GlobalTheory.Mem.WildChar.one_lt_absNorm w; omega
  have := congrArg (fun y : (w.adicCompletion E)ˣ => Valued.v (y : w.adicCompletion E)) hx
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
  exact (pow_eq_one_iff_left h1).1 this

namespace TeichTriv

theorem mul (h : TeichTriv H χ) (h' : TeichTriv H χ') : TeichTriv H (χ * χ') := fun w hw x hx => by
  rw [HChar.loc_mul, h w hw x hx, h' w hw x hx, one_mul]

theorem inv (h : TeichTriv H χ) : TeichTriv H χ⁻¹ := fun w hw x hx => by rw [HChar.loc_inv, h w hw x hx, inv_one]

end TeichTriv

end Host

namespace LamDat

variable {D : D7} (Z : LamDat D)

def Teich : Prop := ∀ a, TeichTriv D.host (Z.chi a)

variable {Z}

end LamDat

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsLamTieFull (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → (∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i) ∧
    ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      (∀ lam : X.abelian₂ i, ∃ (j a : Fin D.R.m) (s : ℕ), IsLam X Z i (atSide X (X.sideL i lam) ι) lam j a s ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)) ∧
      ∀ (j a : Fin D.R.m) (s : ℕ) (b : Bool), 1 ≤ s → s ≤ BlochKatoReduction.Gen.NFun D.R + 1 →
        ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ IsLam X Z i (atSide X b ι) lam j a s ∧
          IsThOf X i (atSide X b ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

variable {X} {Z : LamDat D}

theorem isLamTieFull_of_labels (J A : ∀ i, X.abelian₂ i → Fin D.R.m) (S : ∀ i, X.abelian₂ i → ℕ)
    (hS : ∀ i, X.NonzeroIndexPlace i → ∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i)
    (hι : ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      ∀ lam : X.abelian₂ i, IsLam X Z i (atSide X (X.sideL i lam) ι) lam (J i lam) (A i lam) (S i lam) ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) (S i lam) (Z.kap (J i lam) (A i lam) (S i lam)) (cond0 D.host Z.w0)
          (Z.lam0 (X.l i) (J i lam) (A i lam)))
    (hall : ∀ i, X.NonzeroIndexPlace i → ∀ (j a : Fin D.R.m) (s : ℕ) (b : Bool), 1 ≤ s → s ≤ BlochKatoReduction.Gen.NFun D.R + 1 →
      ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ J i lam = j ∧ A i lam = a ∧ S i lam = s) : IsLamTieFull X Z := fun i hi => by
  obtain ⟨ι, h1, h2⟩ := hι i hi
  refine ⟨hS i hi, ι, h1, fun lam => ⟨_, _, _, h2 lam⟩, fun j a s b hs hs' => ?_⟩
  obtain ⟨lam, rfl, rfl, rfl, rfl⟩ := hall i hi j a s b hs hs'
  exact ⟨lam, rfl, h2 lam⟩

namespace IsLamTieFull

end IsLamTieFull

end Record

end GlobalTheory.LamTie
