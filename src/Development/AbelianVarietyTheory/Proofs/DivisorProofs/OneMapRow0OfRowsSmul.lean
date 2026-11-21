import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

theorem oneMapRow0_of_rows (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ)
    (hpins : OMPins T R κ v₀ O i)
    (hequiv : (O i).EquivAt (κ i) cc)
    (hid : OneMapRow (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (Wc D i)
      (unfBC (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c')) (O i).dict (O i).mu (xiR D) (wtA (κ i))
      (actLev (O i).c' (O i).lev2) (O i).dδ (O i).Cl' (O i).w (O i).La (O i).Nc (O i).gam (O i).vol (O i).ep (O i).io
      (O i).thAd (O i).Plc D.what₂.embLL.toRatAlgHom.fieldRange
      (cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc ph)
    (hrat : (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc ph) :
    OneMapRow0 T R κ v₀ O i :=
  ⟨cc, ph, hequiv, ⟨hpins.1.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O i).hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O i).hle _ _ hpins.2.act.1).2, hid⟩, hrat⟩

end GlobalTheory.OneMapBase
