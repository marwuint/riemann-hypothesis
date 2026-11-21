import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.TotalFrame

attribute [local instance] Over.cartesianMonoidalCategory

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem exists_basis {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∃ b : Module.Basis (Fin m) S (TanM x t.G), ∀ i, b i = tanOf (hv i) := by
  refine ⟨Module.Basis.mk (v := fun i => tanOf (hv i)) (Fintype.linearIndependent_iffₛ.2 fun c c' h => congrFun
    ((hb _ (isTan_tv (∑ i, c i • tanOf (hv i)))).unique ((isComb_iff (fun i => tanOf (hv i)) c _).2 rfl)
      ((isComb_iff (fun i => tanOf (hv i)) c' _).2 h))) fun w _ => ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  obtain ⟨a, ha, -⟩ := hb _ (isTan_tv w)
  rw [(isComb_iff (fun i => tanOf (hv i)) a w).1 ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basis_map {J : Type} [Fintype J] (b : Module.Basis J S (TanM x t.G)) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') :
    ∃ b' : Module.Basis J T (TanM x' t.G), ∀ i, (tv (b' i)).left = spMap (dualMap φ) ≫ (tv (b i)).left := by
  let e := Fintype.equivFin J
  have hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x (fun i => (tv (b.reindex e i)).left) cf w := fun w hw =>
    ⟨(b.reindex e).repr (tanOf hw), (isComb_iff _ _ (tanOf hw)).2 ((b.reindex e).sum_repr _).symm, fun a ha => by
      rw [(isComb_iff _ _ (tanOf hw)).1 ha, Module.Basis.repr_sum_self]⟩
  obtain ⟨b', hb'⟩ := exists_basis (fun i => isTan_map φ hx (isTan_tv (b.reindex e i)))
    (basis_map φ hx (fun i => isTan_tv _) hb)
  refine ⟨b'.reindex e.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb', left_tanOf, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

variable {Dw : Datum H} {l : Level H} {c : Coeff l} {w : Vecs Dw t S} {χ : (E →+* ℂ) → 𝓞 E →+* S}

end Tangent

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W) fun a =>
    GlobalTheory.CoeffRings.mem_of_isIntegral _ (map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a))

variable {Z : Mdl Y i₀} {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}

end Model

end GlobalTheory.TotalFrame
