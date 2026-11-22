import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIntegralFlagModelOfSmoothCoefficientFiel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagAtlasProjectiveEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelProjectiveEmbedding
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FlagSmooth

open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
  GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_gChart_of_flagCover {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (x : Y.X) :
    ∃ M : GChart Y, x ∈ M.U := by
  obtain ⟨z, rfl⟩ := GlobalTheory.BaseVar.surjective_π X x
  have hz : z ∈ (⨆ k, X.F.U k) := by rw [X.F.cover]; trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hz
  exact ⟨X.F.M k, X.F.le k hk⟩

theorem nonempty_atlas_of_cover (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F))
    (hG : ∀ x : Y.X, ∃ M : GChart Y, x ∈ M.U) : Nonempty (Atlas Y p) := by
  classical
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, N, σ, A, C, haff, hle, hCA, htw⟩ := GlobalTheory.TwistEmb.exists_twist_embedding c.F Y.X Y.s (GChart Y)
    (fun j => j.U) (fun j => j.n) (fun j j' => chg j.toMChart j'.toMChart) Y.proj
    (fun x => hG x)
    (fun K _ w j hw => by
      have hh : ⊤ ≤ w ⁻¹ᵁ (j.U ⊓ j.U) := GlobalTheory.TwistEmb.le_inf' w hw hw
      show (chg j.toMChart j.toMChart).map (valF w (j.U ⊓ j.U)) = 1
      rw [map_valF_eq_ev w _ hh, chg_map _ _ w hw hw hh, Module.Basis.toMatrix_self])
    (fun K _ w j j' j'' h1 h2 h3 => by
      show (chg j.toMChart j'.toMChart).map (valF w (j.U ⊓ j'.U)) *
        (chg j'.toMChart j''.toMChart).map (valF w (j'.U ⊓ j''.U)) =
        (chg j.toMChart j''.toMChart).map (valF w (j.U ⊓ j''.U))
      rw [map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h2), map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h2 h3),
        map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h3), chg_map _ _ w h1 h2, chg_map _ _ w h2 h3,
        chg_map _ _ w h1 h3, Module.Basis.toMatrix_mul_toMatrix])
  have hcovL : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x => exists_chart L.isLB x
  have hk : ∀ x : Y.X, ∃ i, ∃ k : ECh Y p, k.M = σ i ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := hcovL x
    obtain ⟨k, h1, h2, h3, h4⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_eCh_le E H Dw l Xo c Y p (σ i) x (hle i hi) (L.U i) hi
    exact ⟨i, k, h1, h2, h3, h4⟩
  choose ix kx hkM hxk haffk hlek using hk
  have hc : IsCompact (Set.univ : Set Y.X) := by
    have e : (Set.univ : Set Y.X) = ⋃ i, ((L.U i : Y.X.Opens) : Set Y.X) :=
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcovL x)).symm
    rw [e]
    exact isCompact_iUnion fun i => (haff i).isCompact
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => ((kx x).V : Set Y.X)) (fun x => (kx x).V.isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxk x⟩)
  have hUM : ∀ i i', L.U i ⊓ L.U i' ≤ (σ i').U ⊓ (σ i).U := fun i i' =>
    le_inf (inf_le_right.trans (hle i')) (inf_le_left.trans (hle i))
  exact ⟨{
    B := t
    fin := inferInstance
    k := fun b => kx b.1
    aff := fun b => haffk b.1
    cov := fun x => by
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨⟨z, hz⟩, hxz⟩
    N := N
    A := fun b => trA (hkM b.1) (hlek b.1) (A (ix b.1))
    C := fun b => trC (hkM b.1) (hlek b.1) (C (ix b.1))
    CA := fun b => trC_mul_trA _ _ _ _ (hCA _)
    tw := fun S _ x b b' h h' hM => tw_tr (hkM b.1) (hkM b'.1) (hlek b.1) (hlek b'.1) (hUM _ _) (A (ix b.1))
      (A (ix b'.1)) (L.g (ix b.1) (ix b'.1)) (fun K _ w hw hw' => htw K w _ _ hw hw') S x h h' hM }⟩

theorem exists_cellModel (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) :
    ∃ (M : FlagModel Y) (g : ∀ en : En Dw.mult, M.YY ⟶ PSpace c.F (plN A.N en.1))
      (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ M.YY)) (_ : ∀ b w, IsOpenImmersion (κ b w)),
      Cells A M.π g κ := by
  have := A.fin
  obtain ⟨Z, π, g, κ, h1, h2, h3, h4, h5, h6⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_properFlag c.F Y.X Y.s (E →+* ℂ) Dw.mult A.N A.B A.V A.alpha A.cv
    A.Dv Y.proj Y.normal (_root_.GlobalTheory.FlagMod.FieldFlag.atlas_isCover E H Dw l Xo c Y p A) A.cov
  have hZ : Cells A π g κ := ⟨h1, h2, h3, h5, h6⟩
  have := h4
  have ht := _root_.GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular E H Dw l Xo c Y p A Z π g κ hZ
  have huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z),
      (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂ := by
    intro S' _ _ P₁ z₁ z₂ e₁ e₂
    refine _root_.GlobalTheory.FlagMod.FieldFlag.hom_ext_of_localization_atPrime S' Z z₁ z₂ fun q => ?_
    obtain ⟨P', hP'⟩ := exists_frMap (IsScalarTower.toAlgHom c.F S' (Localization.AtPrime q.asIdeal)) P₁
    have l₁ := e₁.frMap hP'
    have l₂ := e₂.frMap hP'
    refine _root_.GlobalTheory.FlagMod.FieldFlag.cell_sep E H Dw l Xo c Y p A Z π g κ hZ ht _ _ _ _ l₁.1 l₂.1 fun σ i => ?_
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover
      (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₁)
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover
      (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₂)
    exact (l₁.initSpan_eq hk l₁.1 rfl σ i).symm.trans (l₂.initSpan_eq hk' l₂.1 rfl σ i)
  refine ⟨{ YY := Z, π := π, proper := h1, normal := h2, flat := ?_, F := cellFrames hZ ht
            dense := _root_.GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage E H Dw l Xo c Y p A Z π g κ hZ, top := _root_.GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen E H Dw l Xo c Y p A Z π g κ hZ ht
            rep := fun S _ _ P => ?_, fin := fun K _ _ z => ?_ }, g, κ, h4, hZ⟩
  · exact _root_.GlobalTheory.flat_to_spec_field c.F Z (π ≫ Y.s)
  · obtain ⟨z, hz⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_lies_of_local E H Dw l Xo c Y p A Z π g κ hZ ht S P huniq fun q =>
      _root_.GlobalTheory.FlagMod.FieldFlag.exists_cell_lies E H Dw l Xo c Y p A Z π g κ hZ ht S P q
    exact ⟨z, hz, fun z' hz' => huniq S P z' z hz' hz⟩
  · refine (Set.finite_singleton z).subset fun z' ⟨hx, h⟩ => ?_
    exact _root_.GlobalTheory.FlagMod.FieldFlag.cell_sep E H Dw l Xo c Y p A Z π g κ hZ ht K z' z _ hx rfl h

theorem smooth_proj_flagStr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (T : GlobalTheory.CompHS.TorFlag Xo c), ∃ d : ℕ, SmoothOfRelativeDimension d (GlobalTheory.CompHS.flagStr T.X) ∧ IsProjOver (GlobalTheory.CompHS.flagStr T.X) := by
  intro E _ _ _ H D l Xo c T
  obtain ⟨p⟩ := GlobalTheory.FlagMod.LowRank.nonempty_proj_id (E := E) (c := c)
  obtain ⟨A⟩ := nonempty_atlas_of_cover T.Y p (exists_gChart_of_flagCover T.X)
  obtain ⟨M, g, κ, hκ, hZ⟩ := exists_cellModel T.Y p A
  obtain ⟨d, hsm, hpr⟩ := _root_.GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj E H D l Xo c T.Y p A M.YY M.π g κ hκ hZ T.smooth
  obtain ⟨h, hh, hπ⟩ := _root_.GlobalTheory.CompanionTheory.FlagMod.flagModel_iso_cells E H D l Xo c T.Y p A M g κ hκ hZ T.smooth T.flag
  have e : flagStr T.X = h ≫ M.π ≫ T.Y.s := by
    rw [← Category.assoc, hπ]
  refine ⟨d, ?_, ?_⟩
  · rw [e]; exact GlobalTheory.VarFlag.smooth_iso h _ hsm
  · rw [e]
    obtain ⟨N, i, hi, hs⟩ := hpr
    exact ⟨N, h ≫ i, inferInstance, by rw [Category.assoc, hs]⟩

end GlobalTheory.CompanionTheory.FlagSmooth
