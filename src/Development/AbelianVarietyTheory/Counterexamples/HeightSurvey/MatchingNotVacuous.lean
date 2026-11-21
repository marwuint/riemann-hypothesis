import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

namespace GlobalTheory.ThetaFrameCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem genFibre_tied (T : CDVR) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt)
    (G : SAB H (Sp T.V)) (m : SABMap G Y.t yt) :
    ∃ (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _))
      (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (m' : SABMap t' Y.oF.t z),
      m1.φ = m'.φ ≫ Y.m0.toSABMap.φ ∧ m2.φ ≫ m.φ = m'.φ ≫ Y.m.φ := by
  obtain ⟨PP', cub, sym, adj, prim, m2, -⟩ :=
    sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T.V T.Fr)) G
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ yt (spMap (algebraMap T.V T.Fr)) m m2
  have cancel : ∀ (t' : SAB H (Sp T.Fr)) (p : Sp T.Fr ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' Y.oF.t z, n.φ = m'.φ ≫ Y.m.φ := by
    intro t' p hp n; subst hp
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n
  obtain ⟨m', hm'⟩ := cancel _ _ hz.symm n
  obtain ⟨m1, h1⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ (pullback.fst _ _) z Y.m0.toSABMap m'
  exact ⟨_, m1, m2, m', h1, hn.symm.trans hm'⟩

variable {Xo}

end GlobalTheory.ThetaFrameCheck
