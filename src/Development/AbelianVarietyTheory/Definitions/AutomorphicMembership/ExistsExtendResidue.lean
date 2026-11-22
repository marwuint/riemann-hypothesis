import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam GlobalTheory.TotalFrame GlobalTheory.FlagPts Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop}

open Classical in

def FlagFam.lat {Z : Mdl Y i₀} (s : FlagFam P Z) : Lat Z := if h : ∃ L : Lat Z, s.1 = allSteps L then h.choose else Lat.top Z

open Classical in
variable (P) in

def classFam (Z : Mdl Y i₀) : FlagFam P Z :=
  if h : ∃ L, P Z L then FlagFam.full h.choose (.inr h.choose_spec) else FlagFam.empty Z

def Mdl.inclV (Z : Mdl Y i₀) : i₀.c.V W →+* Z.i.c.V W :=
  ((IntermediateField.inclusion Z.le).toRingHom.comp (i₀.c.V W).subtype).codRestrict _ fun a => a.2

theorem Mdl.isLocalHom_inclV (Z : Mdl Y i₀) : IsLocalHom Z.inclV := ⟨fun a ha => by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 ha
  have hc : ((a : i₀.c.F) : ℂ) * ((b : Z.i.c.F) : ℂ) = 1 := congrArg (fun z : Z.i.c.V W => ((z : Z.i.c.F) : ℂ)) hb
  have h₀ : (a : i₀.c.F) ≠ 0 := fun h => by simp [h] at hc
  refine isUnit_iff_exists_inv.2 ⟨⟨(a : i₀.c.F)⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ h₀)⟩
  change ((a : i₀.c.F) : ℂ)⁻¹ ∈ W
  rw [← eq_inv_of_mul_eq_one_right hc]
  exact b.2⟩

theorem exists_extend_residue {R R' k : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    [Finite (ResidueField R')] [Field k] [IsAlgClosed k] (f : R →+* R') [IsLocalHom f] (ψ : ResidueField R →+* k) :
    ∃ φ : R' →+* k, φ.comp f = ψ.comp (residue R) := by
  letI := (ResidueField.map f).toAlgebra
  letI := ψ.toAlgebra
  have : Module.Finite (ResidueField R) (ResidueField R') := .of_finite
  let χ : ResidueField R' →ₐ[ResidueField R] k := IsAlgClosed.lift
  exact ⟨χ.toRingHom.comp (residue _), RingHom.ext fun a => χ.commutes (residue _ a)⟩

theorem finite_quot_smul_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite ℤ M] {n : ℕ}
    (hn : n ≠ 0) : Finite (M ⧸ (Ideal.span {(n : R)} • ⊤ : Submodule R M)) := by
  have key (P : Submodule R M) (hP : ∀ a, n • a ∈ P) : Finite (M ⧸ P) := by
    have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
    have : AddGroup.FG (M ⧸ P) := AddGroup.fg_of_surjective (f := P.mkQ.toAddMonoidHom) P.mkQ_surjective
    refine AddCommGroup.finite_of_fg_torsion _ fun x => isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
    obtain ⟨a, rfl⟩ := P.mkQ_surjective x
    rw [← map_nsmul]
    exact (Submodule.Quotient.mk_eq_zero P).2 (hP a)
  refine key _ fun a => ?_
  rw [← Nat.cast_smul_eq_nsmul R]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial

end Family

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

section Reduction

abbrev V₀ : Type := κ.c.V ct.W

abbrev kbar : Type := AlgebraicClosure (ResidueField ct.V₀)

def ρ₀ : ct.V₀ →+* ct.kbar := (algebraMap (ResidueField ct.V₀) ct.kbar).comp (residue ct.V₀)

instance charP_kbar : CharP ct.kbar p := by
  have := Fact.mk ct.hp
  refine (CharP.charP_iff_prime_eq_zero ct.hp).2 ?_
  rw [← map_natCast ct.ρ₀, ρ₀, RingHom.comp_apply, map_eq_zero, residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  simpa using SharedLaws.mem_nonunits_V κ.c ct.hp.ne_zero ct.hW

abbrev LaBar : Type := ct.kbar ⊗[ℤ] S.Dw.La

def eigLat (σ : D.host.E →+* ℂ) : Submodule ct.V₀ (ct.V₀ ⊗[ℤ] S.Dw.La) :=
  eigenSub (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* _)) (embV κ.c ct.W σ)

def redLa : ct.V₀ ⊗[ℤ] S.Dw.La →ₗ[ℤ] ct.LaBar := ct.ρ₀.toIntAlgHom.toLinearMap.rTensor S.Dw.La

def eigBar (τ : PsiT D) : Submodule ct.kbar ct.LaBar := Submodule.span ct.kbar (ct.redLa '' ct.eigLat (embOf D τ))

instance : FiniteDimensional ct.kbar ct.LaBar :=
  have := S.Dw.fin
  have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
  Module.Finite.base_change ℤ _ _

abbrev FlP : Type := Flags ct.kbar fun τ : PsiT D => ↥(ct.eigBar τ)

def FlP.sub {ct : At S κ p} (F : ct.FlP) (τ : PsiT D) (i : ℕ) : Submodule ct.kbar ct.LaBar :=
  (F.step τ i).map (ct.eigBar τ).subtype

abbrev LaP (_ct : At S κ p) : Type :=
  S.Dw.La ⧸ (Ideal.span {(p : 𝓞 D.host.E)} • ⊤ : Submodule (𝓞 D.host.E) S.Dw.La)

def Sum1 : Type := {l : Submodule (𝓞 D.host.E) ct.LaP // (∃ l', IsCompl l l') ∧
  Nonempty (l ≃ₗ[𝓞 D.host.E] (𝓞 D.host.E ⧸ Ideal.span {(p : 𝓞 D.host.E)}))}

def Sum1.bar {ct : At S κ p} (l : ct.Sum1) : Submodule ct.kbar ct.LaBar :=
  Submodule.span ct.kbar {s | ∃ a : S.Dw.La, Submodule.Quotient.mk a ∈ l.1 ∧ s = 1 ⊗ₜ a}

def psiBar : LinearMap.BilinForm ct.kbar ct.LaBar := S.Dw.EF.baseChange ct.kbar

def locus (l : ct.Sum1) : Closeds ct.FlP :=
  between j (fun τ => l.bar.submoduleOf (ct.eigBar τ)) fun τ => (ct.psiBar.orthogonal l.bar).submoduleOf (ct.eigBar τ)

theorem FlP.ext {ct : At S κ p} {F F' : ct.FlP} (h : ∀ τ i, F.sub τ i = F'.sub τ i) : F = F' :=
  Flags.ext fun τ i => Submodule.map_injective_of_injective (ct.eigBar τ).injective_subtype (h τ i)

instance finite_summands : Finite ct.Sum1 := by
  have := S.Dw.fin
  have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
  have : Finite ct.LaP := finite_quot_smul_top ct.hp.ne_zero
  have : Finite (Submodule (𝓞 D.host.E) ct.LaP) := Finite.of_injective _ SetLike.coe_injective
  exact Subtype.finite

end Reduction

section Point

variable {Z : ct.Mdl} (y : ct.Pt Z)

def LevelMatch (t : (htpTrue ct).Tp y) (a : S.Dw.La) : Prop :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  (Tate.lev t 1).left ≫ abVarι y.P = y.P.y ≫ ((ct.Y Z.i).oF.etaA a ^ (Z.i.l.A / p)).left

def redGraph (ρ : ↥(intO ↥y.C.S) →+* ct.kbar) : AddSubgroup ((htpTrue ct).TC y × ct.LaBar) :=
  AddSubgroup.closure {q | ∃ (c : ↥(intO ↥y.C.S)) (t : (htpTrue ct).Tp y) (a : S.Dw.La), ct.LevelMatch y t a ∧
    q = ((show (ct.fld y).C from c.1) • (htpTrue ct).iT y t, ρ c ⊗ₜ a)}

def redSub (ρ : ↥(intO ↥y.C.S) →+* ct.kbar) (F : Submodule (ct.fld y).C ((htpTrue ct).TC y)) :
    Submodule ct.kbar ct.LaBar := Submodule.span ct.kbar {s | ∃ w ∈ F, (w, s) ∈ ct.redGraph y ρ}

end Point

def SpPt (Z : ct.Mdl) : Type :=
  {x : Sp ct.kbar ⟶ Z.X // x ≫ Z.s ≫ spMap Z.inclV = spMap ct.ρ₀}

instance nonempty_spPt (Z : ct.Mdl) : Nonempty (ct.SpPt Z) := by
  have := Z.i.c.fin
  have : NumberField Z.i.c.F := NumberField.mk
  obtain ⟨-, h₂⟩ := GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V ct.W) ct.hp.ne_zero
    (SharedLaws.mem_nonunits_V Z.i.c ct.hp.ne_zero ct.hW)
  have := Z.isLocalHom_inclV
  obtain ⟨φ, hφ⟩ := exists_extend_residue Z.inclV (algebraMap _ ct.kbar)
  obtain ⟨x, hx⟩ := Z.exists_point (one_le_two.trans (S.two_le.trans S.rank_eq.ge)) φ
  exact ⟨x, by rw [reassoc_of% hx, spMap_comp_spMap, hφ, ρ₀]⟩

instance nonempty_curve (Z : ct.Mdl) : Nonempty (Curve ct.Fbar Z.X) := by
  have := Fact.mk ct.hp
  have := Z.i.c.fin
  have : NumberField Z.i.c.F := NumberField.mk
  have hV := SharedLaws.mem_nonunits_V Z.i.c ct.hp.ne_zero ct.hW
  obtain ⟨-, h₂⟩ := GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V ct.W) ct.hp.ne_zero hV
  have : CharP (ResidueField (Z.i.c.V ct.W)) p := (CharP.charP_iff_prime_eq_zero ct.hp).2 (by
    rw [← map_natCast (residue _), residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    simpa using hV)
  letI := ZMod.algebra (ResidueField (Z.i.c.V ct.W)) p
  letI := ZMod.algebra ct.Fbar p
  let ψ : ResidueField (Z.i.c.V ct.W) →ₐ[ZMod p] ct.Fbar := IsAlgClosed.lift
  obtain ⟨x, -⟩ := Z.exists_point (one_le_two.trans (S.two_le.trans S.rank_eq.ge)) (ψ.toRingHom.comp (residue _))
  exact Curve.nonempty_of_point x

end At

end GlobalTheory.LocM
