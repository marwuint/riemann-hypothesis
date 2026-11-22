import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

namespace GlobalTheory.SplitPairLift

theorem isIrreducible_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (χ : G →* ℂˣ) : (twist ρ χ).IsIrreducible := by
  let e : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at h1⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 h

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detIrr (n : ℕ) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 h.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth h.detChar
  irr := isIrreducible_twist π.irr _

theorem twist_twist_inv {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) :
    twist (twist π.π (detChar (Fin n) χ)) (detChar (Fin n) χ⁻¹) = π.π := by
  rw [twist_twist]
  have : detChar (Fin n) χ⁻¹ * detChar (Fin n) χ = 1 := by
    ext g; simp
  rw [this, twist_one]

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem e_spehLoc (T : WDTie N A) (p : Part A.CG) (w : PlE H) :
    T.e w (spehLoc N A p w) = speh (T.e w (A.locG p.π w)) p.d := by
  unfold spehLoc speh
  generalize ((p.d : ℝ) - 1) / 2 = s
  have key : ∀ L : List ℝ,
      T.e w (L.foldr (fun j acc => A.lpSum (A.lpTw (A.locG p.π w) (s - j)) acc) (A.lpZero w)) =
        L.foldr (fun j acc => ((T.e w (A.locG p.π w)).lpTw (s - j)).lpSum acc) (WD.lpZero _) := by
    intro L
    induction L with
    | nil => exact T.zero w
    | cons j l ih => rw [List.foldr_cons, List.foldr_cons, T.sum, T.tw, ih]
  exact key _

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitPairLift
