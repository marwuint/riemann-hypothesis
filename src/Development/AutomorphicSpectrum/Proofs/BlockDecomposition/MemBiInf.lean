import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.DisoHm

section Nest
variable {D : Type 1} [Category.{0} D]

abbrev nestF {P P₂ : ObjectProperty D} {Pn : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, P₂ T → ∃ hp : P T, Pn ⟨T, hp⟩) : P₂.FullSubcategory ⥤ Pn.FullSubcategory :=
  Pn.lift (P.lift P₂.ι fun T => (h₁ _ T.property).1) fun T => (h₁ _ T.property).2

def nestAdj {P P₂ : ObjectProperty D} {Pn : ObjectProperty P.FullSubcategory}
    (h₁ : ∀ T, P₂ T → ∃ hp : P T, Pn ⟨T, hp⟩) (h₂ : ∀ T : Pn.FullSubcategory, P₂ T.obj.obj) :
    nestF h₁ ⊣ (P₂.lift (Pn.ι ⋙ P.ι) h₂) :=
  (CategoryTheory.Equivalence.mk (nestF h₁)
    (P₂.lift (Pn.ι ⋙ P.ι) h₂) (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))).toAdjunction

end Nest

theorem mem_biInf {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (x : X) :
    x ∈ (⨅ α ∈ S, U α) ↔ ∀ α ∈ S, x ∈ U α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.iInf_insert]
    simp [ih]

section St
variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := fun _ _ => trivial

theorem st_inf (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (U : Cov q) (S : Finset U.ι) (hS : S.Nonempty)
    (T : Thick (nlFun γ p X q κ)) :
    St Q {⨅ α ∈ S, U.U α} T ↔ St Q (Set.range U.U) T ∧ ∀ α ∈ S, InU (U.U α) T := by
  constructor
  · rintro ⟨h1, V, rfl, hV⟩
    have h2 : ∀ α ∈ S, InU (U.U α) T := fun α hα x hx =>
      ((mem_biInf U.U S _).1 (hV hx)) α hα
    obtain ⟨α, hα⟩ := hS
    exact ⟨⟨h1, U.U α, ⟨α, rfl⟩, h2 α hα⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, _, rfl, fun x hx => (mem_biInf U.U S _).2 fun α hα => h2 α hα hx⟩

end St

section Top
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

def resO {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (hle : Q' ≤ Q) (c : b.R) :
    CH.Mor (sq (IdF.top (sP Q).A) (stdI Q none c)) (sq (IdF.top (sP Q').A) (stdI Q' none c)) (RingHom.id _) :=
  (incl hle).sq (fun _ _ _ => trivial) (incl_std hle none c)

theorem std0 {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (T : Q.FullSubcategory) :
    (IdF.top (sP Q).A).S T = (stdI Q (some 0) 0).S T := by
  have : (sFil Q 0).S T = ⊤ := T.obj.pdPow_zero
  exact (top_le_iff.1 (this.ge.trans le_sup_left)).symm

end Top

end GlobalTheory.CompanionTheory.DisoHm
