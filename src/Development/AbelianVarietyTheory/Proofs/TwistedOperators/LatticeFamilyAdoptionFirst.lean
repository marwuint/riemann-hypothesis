import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalRingCardinality.DataNChTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionFieldEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso

namespace LinearIndependenceOfCarries
section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ReadingExt

open Module

theorem li_of_carries {LL K WL V : Type} [Field LL] [Field K] [AddCommGroup WL] [Module LL WL] [AddCommGroup V] [Module K V]
    {emb : LL →+* K} (e : WL →ₛₗ[emb] V)
    (hC : ∀ (ι : Type) (b : Basis ι LL WL), ∃ c : Basis ι K V, ∀ i, c i = e (b i))
    {ι : Type} {v : ι → WL} (hv : LinearIndependent LL v) : LinearIndependent K (fun a => e (v a)) := by
  have hs := hv.linearIndepOn_id
  obtain ⟨c, hc⟩ := hC _ (Basis.extend hs)
  have hsub := hs.subset_extend (Set.subset_univ _)
  let f : ι → ↥(hs.extend (Set.subset_univ _)) := fun a => ⟨v a, hsub ⟨a, rfl⟩⟩
  have hf : Function.Injective f := fun a b h => hv.injective (congrArg Subtype.val h)
  have h2 := c.linearIndependent.comp f hf
  have h3 : (c ∘ f) = fun a => e (v a) := by
    funext a
    simp only [Function.comp, hc, Basis.extend_apply_self, f]
  rwa [h3] at h2

theorem comp_cast_of_heq {K : Type} {a b : ℕ} (h : b = a) (z : Fin a → K) (y : Fin b → K) (hz : HEq z y) :
    z ∘ finCongr h = y := by
  subst h
  exact eq_of_heq hz

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in
set_option synthInstance.maxHeartbeats 400000 in

theorem fracExt_algebraMap (c : NChoice D) (w : D.what₂.places.Pl) (x : D.ntw.O (c.twI w)) :
    fracExt c w (algebraMap _ (FractionRing (D.ntw.O (c.twI w))) x) =
      algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) x := by
  rw [IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (c.Oe w) (FractionRing (c.Oe w))]
  simp [fracExt, IsFractionRing.map]

end GlobalTheory.CompanionTheory.ReadingExt

end
end

end LinearIndependenceOfCarries
