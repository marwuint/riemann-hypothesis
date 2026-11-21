import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBasisNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.Spread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open GlobalTheory.LieMet (tan_ext)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_germs {X : Scheme.{0}} (y : X) {W : X.Opens} (hW : y ∈ W) {κ : Type} [Finite κ]
    (a : κ → X.presheaf.stalk y) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (hy : y ∈ U) (s : κ → Γ(X, U)), U ≤ W ∧
      ∀ i, X.presheaf.germ U y hy (s i) = a i := by
  choose V hV s hs using fun i => X.presheaf.exists_germ_eq (a i)
  have ho : IsOpen ((W : Set X) ∩ ⋂ i, (V i : Set X)) :=
    W.isOpen.inter (isOpen_iInter_of_finite fun i => (V i).isOpen)
  obtain ⟨U, hU, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⟨_, ho⟩) (x := y)
    ⟨hW, Set.mem_iInter.2 hV⟩
  have hl : ∀ i, U ≤ V i := fun i z hz => Set.mem_iInter.1 (hle hz).2 i
  exact ⟨U, hU, hy, fun i => X.presheaf.map (homOfLE (hl i)).op (s i), fun z hz => (hle hz).1,
    fun i => (X.presheaf.germ_res_apply (homOfLE (hl i)) y hy (s i)).trans (hs i)⟩

theorem spMap_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U) :
    spMap (X.presheaf.germ U y hy).hom ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec) =
      (show Sp (X.presheaf.stalk y) ⟶ X from X.fromSpecStalk y) :=
  hU.fromSpecStalk_eq_fromSpecStalk hy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem exists_bc {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* S) {φ' : c.F →+* S}
    {x' : Sp S ⟶ Z.X} (hφ : ψ.comp φ = φ') (hx : spMap ψ ≫ x = x') :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.vec τ i = res ψ hx (f.vec τ i) := by
  subst hφ hx
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z R S φ x f ψ
  exact ⟨g, fun τ i => tan_ext (hg τ i)⟩

theorem exists_coord {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ A B : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, B * A = 1 ∧ ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k := by
  choose A hA _ using fun i => f.existsUnique_sum τ (g.vec τ i) (g.act_vec τ i)
  choose B hB _ using fun i => g.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)
  refine ⟨Matrix.of A, Matrix.of B, Matrix.ext fun i => congrFun ?_, hA⟩
  refine (f.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)).unique ?_ ?_
  · refine (hB i).trans ?_
    simp only [show ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k from hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    exact Finset.sum_comm
  · simp only [Matrix.one_apply, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_smul R]

theorem exists_change {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (A B : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (h : ∀ τ, B τ * A τ = 1) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.vec τ i = ∑ k, A τ i k • f.vec τ k := by
  have hs : ∀ τ (a : Fin (Dw.mult τ) → R), ∑ i, a i • ∑ k, A τ i k • f.vec τ k =
      ∑ k, (Matrix.vecMul a (A τ)) k • f.vec τ k := fun τ a => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  refine ⟨EigFrame.ofVec (fun τ i => ∑ k, A τ i k • f.vec τ k) (fun τ i a => ?_) fun τ w hw => ?_,
    fun τ i => tan_ext rfl⟩
  · simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · obtain ⟨a, ha, hu⟩ := f.existsUnique_sum τ w hw
    refine ⟨Matrix.vecMul a (B τ), ?_, fun b hb => ?_⟩
    · show w = _
      rw [hs, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
      exact ha
    · rw [← hu _ (hb.trans (hs τ b)), Matrix.vecMul_vecMul, mul_eq_one_comm.1 (h τ), Matrix.vecMul_one]

end GlobalTheory.ShFam.Spread
