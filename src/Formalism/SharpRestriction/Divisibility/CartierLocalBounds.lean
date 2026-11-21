import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.MainNotions.CartierLocalBounds

open Formalism.BasicNotions

section Jets

variable {C : Type} [Field C]

def mvExp {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun m => ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C)

end Jets

structure LocD (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d] where

  five_le_l : 5 ≤ l

  d_even : Even d

  r : ℕ
  j : ℕ
  j' : ℕ
  rh : ℕ
  rh_le : rh ≤ j'

  rh_le_big : rh + j' ≤ r
  jj_le : j + j' ≤ r

  big : Fin 2 → ZMod d → Prop

  rk : Fin 2 → ZMod d → ℕ
  rk_big : ∀ g a, big g a → rk g a = r - j'
  rk_small : ∀ g a, ¬ big g a → rk g a = j'

  U : ∀ g a, Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])
  U_summand : ∀ g a, big g a → ∃ Q : Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l]), IsCompl (U g a) Q
  U_basis : ∀ g a, big g a → Nonempty (Module.Basis (Fin (r - j' - j)) 𝓞_ℂ_[l] (U g a))

  Chart : Type

  tan : Chart → ∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])

  chart_tan : ∀ b : (∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])),
    ∃ χ : Chart, tan χ = b

  alC : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk g a) → ℂ_[l]
  alC_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → alC χ g b c s a = 0

  alC_zero : ∀ χ g b c k, alC χ g b c 0 b k = ((tan χ g b c k : 𝓞_ℂ_[l]) : ℂ_[l])

  beP : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk (1 - g) a) → ℂ_[l]
  beP_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → beP χ g b c s a = 0

  beP_zero : ∀ χ g b c a, beP χ g b c 0 a = 0

  chart_mod : ∀ (χ : Chart)
    (x : ∀ g : Fin 2, ℕ → (Σ b : ZMod d, Fin (rk g b)) → (Σ b : ZMod d, Fin (rk g b)) → 𝓞_ℂ_[l]),
    (∀ g (s : ℕ) c b, b.1 ≠ c.1 + (s : ZMod d) → x g s c b = 0) →
    (∀ g, IsUnit (Matrix.of (x g 0)).det) →
    ∃ χ' : Chart,
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, alC χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * alC χ g b.1 b.2 (n - s) a k) ∧
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, beP χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * beP χ g b.1 b.2 (n - s) a k)

  tL : Chart → ∀ (g : Fin 2) (a : ZMod d), (Σ b : ZMod d, Fin (rk g b)) → MvPowerSeries (Fin (rk g a)) ℂ_[l]
  tL_const : ∀ χ g a x, MvPowerSeries.constantCoeff (tL χ g a x) = 0

  tL_log_same : ∀ χ g a (k : Fin (rk g a)) (μ : Fin (rk g a) →₀ ℕ),
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) =
      if μ = Finsupp.single k 1 then 1 else 0

  tL_log_other : ∀ χ g a a' (k : Fin (rk g a')) (μ : Fin (rk g a) →₀ ℕ), a' ≠ a →
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a' k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) = 0

  hL : ∀ (g : Fin 2) (a a' : ZMod d), MvPowerSeries (Fin (rk g a) ⊕ Fin (rk (1 - g) a')) ℂ_[l]

  Tt : Fin 2 → Type
  [instTt : ∀ g, AddCommGroup (Tt g)]
  [modTt : ∀ g, Module ℤ_[l] (Tt g)]
  Tt_free : ∀ g, Module.Free ℤ_[l] (Tt g)
  Tt_rank : ∀ g, Module.finrank ℤ_[l] (Tt g) = d * (r - rh)

  alHT : ∀ g, Tt g → ∀ a, (Fin (rk g a) → 𝓞_ℂ_[l]) →ₗ[𝓞_ℂ_[l]] 𝓞_ℂ_[l]

  chiG : Chart → ∀ g, Tt g → MvPowerSeries (Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l]

  chiG_leaf : ∀ χ g (t : Tt g) a,
    MvPowerSeries.subst (fun x => tL χ g a x)
        (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) (chiG χ g t)) =
      mvExp (∑ k : Fin (rk g a), ((alHT g t a (Pi.single k 1) : 𝓞_ℂ_[l]) : ℂ_[l]) •
        (MvPowerSeries.X k : MvPowerSeries (Fin (rk g a)) ℂ_[l]))

  ev : Chart → ∀ N : ℕ,
    MvPolynomial (Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (rk g a)) 𝓞_ℂ_[l] →
    MvPowerSeries (Fin N × Σ g : Fin 2, Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l] → ℂ_[l]

attribute [instance] LocD.instTt LocD.modTt

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def Alternating : Prop := ∀ a : ZMod d, (Λ.big 0 a ↔ Even a.val) ∧ (Λ.big 1 a ↔ ¬ Even a.val)

end LocD

namespace LocD

end LocD

namespace LocD

end LocD

def PtCl (D : Formalism.BasicNotions.D7) (Y : ModuliIntegralCharts.Prov D) (w : Y.Dat) (l : ℕ) [Fact l.Prime] : Type :=
  Σ y : (Y.loc w l).Pt (Y.loc w l).YY,
    {e : ((Y.loc w l).fld y).C ≃+* ℂ_[l] // ∀ x, ‖e x‖ = ‖x‖}

structure Loc (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) where

  dat : ℕ → Y.Dat
  dat_rk : ∀ j, 1 ≤ j → j < D.R.m → Y.rk (dat j) = D.R.r
  dat_jj : ∀ j, 1 ≤ j → j < D.R.m → Y.jj (dat j) = D.R.k + j - 1

  Pt : D.jet.Sit → Type

  la : ∀ i, Pt i → X.PlP (D.jet.loc i).l

  ty : ∀ i, Pt i → ZMod (D.jet.loc i).d → DV.Emb D (D.jet.loc i).l
  ty_succ : ∀ i y a, ty i y (a + 1) = DV.phiPow D 1 (ty i y a)
  ty_inj : ∀ i y, Function.Injective (ty i y)

  ptE : ∀ i, D.jet.jOf i < D.R.m → Pt i ≃ PtCl D Y (dat (D.jet.jOf i)) (D.jet.loc i).l

  loc : ∀ i, Pt i → LocD (D.jet.loc i).l (D.jet.loc i).d

  loc_r : ∀ i y, (loc i y).r = D.R.r
  loc_j : ∀ i y, (loc i y).j = D.jet.jOf i
  loc_j' : ∀ i y, (loc i y).j' = D.R.m - D.jet.jOf i

  loc_big : ∀ i y a,
    ((loc i y).big 0 a ↔ ty i y a ∈ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y))) ∧
    ((loc i y).big 1 a ↔ ty i y a ∉ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y)))

  loc_alt : ∀ i y, (loc i y).Alternating

  loc_rh : ∀ i (h : D.jet.jOf i < D.R.m) (y : Pt i),
    Module.finrank ℤ ((Y.loc (dat (D.jet.jOf i)) (D.jet.loc i).l).Ylat (ptE i h y).1) =
      2 * D.R.f * (loc i y).rh

variable (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) (Lc : Loc D X Y)

end Formalism.MainNotions.CartierLocalBounds
