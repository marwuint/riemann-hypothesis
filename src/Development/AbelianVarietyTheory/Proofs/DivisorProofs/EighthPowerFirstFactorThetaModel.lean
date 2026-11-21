import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotent
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectionsEighthPowerGrpObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerOfMatrixUnitsIdempotentSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixUnitsExtendNormalNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGrpPullbackOfCompatibleRetracts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianPullbackAbelianOverOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfEighthPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianFunctionFieldModelArithBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedSiegelModuliOverIntegers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SiegFactor.firstFactor : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE) (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), S.Over₀ M U₀ → OpenAt F β u M U c → ∃ (G : Over M.Z) (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left) (_ : IsCommMonObj G), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ LBIso (hodge Zh.G S.g) (lbPow (hodge G g) 8) := by
  intro g n hg hn hodd F W hW o Ω _ _ _ _ β S ρ u hsys M U₀ EE Zh U c hO hOpen
  obtain ⟨-, -, hSg, ⟨c', hc'pb, pr, hpr, huniv, -⟩, -⟩ := hsys
  haveI : IsCommMonObj ρ.P.A := ρ.P.isAb.comm
  obtain ⟨inj, hinj, hinjpr, hsum⟩ := _root_.GlobalTheory.eighthPower_inj_exists ρ.P.A c'.A pr hpr huniv
  let E' : Fin 8 → Fin 8 → (ρ.P.A ⟶ ρ.P.A) := fun a b => pr a ≫ inj b
  have hE' : ∀ a b, IsMonHom (E' a b) := fun a b => by
    haveI := hpr a; haveI := hinj b; exact inferInstanceAs (IsMonHom (pr a ≫ inj b))
  have hrel' : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1 := by
    intro a b c d
    show (pr a ≫ inj b) ≫ pr c ≫ inj d = if b = c then pr a ≫ inj d else 1
    rw [Category.assoc, ← Category.assoc (inj b), hinjpr]
    split_ifs
    · rw [Category.id_comp]
    · haveI := hinj d; rw [MonObj.one_comp, MonObj.comp_one]
  haveI : AlgebraicGeometry.IsNoetherian M.Z := _root_.GlobalTheory.ratModel_isNoetherian_of_arithBase M
  have hdense : Dense (U₀ : Set M.Z) := U₀.isOpen.dense hO.ne
  obtain ⟨E, hE, hrel, hsumE, hcompat⟩ := _root_.GlobalTheory.EighthPowerUnits.exists_matrixUnits_extend hO.normal U₀ hdense Zh.G Zh.semi
    ((Over.pullback Zh.u₀).obj ρ.P.A) ρ.P.A Zh.u₀ Zh.φ (pullback.fst _ _) Zh.cart (isGrpPullback_pullback _ _)
    E' hE' hrel' hsum
  have hidem : E 0 0 ≫ E 0 0 = E 0 0 := by rw [hrel]; simp
  obtain ⟨H, _, i, r, hi, hr, hir, hri, hH⟩ := _root_.GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image M.Z Zh.G Zh.semi (E 0 0) (hE 0 0) hidem
  haveI : IsCommMonObj H := hH.comm
  have huniv8 := _root_.GlobalTheory.matUnits_univ_of_idem Zh.G H E hE hrel hsumE i r hi hr hir hri
  have hpr8 : ∀ a, IsMonHom (E a 0 ≫ r) := fun a => by
    haveI := hE a 0; haveI := hr; exact inferInstanceAs (IsMonHom (E a 0 ≫ r))
  have hdimG : SmoothOfRelativeDimension (8 * g) Zh.G.hom := hSg ▸ Zh.dim
  have hdim : SmoothOfRelativeDimension g H.hom := _root_.GlobalTheory.PowDim.smoothOfRelativeDimension_of_eighthPower H Zh.G g (fun a => E a 0 ≫ r) huniv8 hH hdimG
  have hhodge := _root_.GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight M.Z H Zh.G g (fun a => E a 0 ≫ r) hpr8 huniv8 hH hdim
  obtain ⟨e', he'm, h1, h2⟩ := hcompat 0 0
  obtain ⟨C', _, a, b, ha, hb⟩ := _root_.GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts U₀.ι Zh.u₀ Zh.G ((Over.pullback Zh.u₀).obj ρ.P.A) ρ.P.A Zh.φ
    (pullback.fst _ _) Zh.cart (isGrpPullback_pullback _ _) (E 0 0) (E' 0 0) e' he'm h1 h2 H i r hi hr hir hri
    c'.A (inj 0) (pr 0) (hinj 0) (hpr 0) (by simpa using hinjpr 0 0) rfl
  obtain ⟨φ', φ₂, hφ', -, -, -⟩ := hc'pb
  obtain ⟨e, he⟩ := _root_.GlobalTheory.FactorOverOpen.factor_over_open hO.normal (_root_.GlobalTheory.SepSiegel.isSeparated_toZ F) F.univ.A F.univ.ab H hH U₀ U hO.ne hOpen.1
    (Zh.u₀ ≫ u) c C' a (b ≫ φ') ha (hb.comp hφ') Ω M.pt M.gen (fun x y hx hy => by
      rw [hOpen.2.2.2.2 x hx, ← Category.assoc, Zh.u₀_gen y hy])
  refine ⟨H, inferInstance, e, inferInstance, hH, hdim, he, ?_⟩
  rw [hSg]
  exact hhodge
