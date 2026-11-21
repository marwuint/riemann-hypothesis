import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B DividedPowers

namespace CompanionTheory.KM.G4

variable (k : Type) [Field k]

structure SmV where
  X : Scheme.{0}
  q : X ⟶ Spec (CommRingCat.of k)
  d : ℕ
  smooth : SmoothOfRelativeDimension d q
  proper : IsProper q

variable {k} (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I)

abbrev OY (Y : SmV k) : Thick ((schFn Y.q).cr b ht κ) ⥤ CommAlgCat.{0} b.R := OA _ (RingHom.id b.R)

abbrev Hc (Y : SmV k) (n : ℕ) : Type 1 := CH.H (CH.modF (OY b ht κ Y)) n

def schPt {Y Y' : SmV k} (u : Y'.X ⟶ Y.X) (hu : u ≫ Y.q = Y'.q) : (schFn Y'.q).ptK κ ⟶ (schFn Y.q).ptK κ where
  app B := TypeCat.ofHom fun z => ⟨(z.1.1, z.1.2 ≫ u), by
    obtain ⟨⟨f, y⟩, h⟩ := z
    change y ≫ Y'.q = _ at h
    change (y ≫ u) ≫ Y.q = _
    exact (Category.assoc y u Y.q).trans ((congrArg (fun t => y ≫ t) hu).trans h)⟩
  naturality B B' φ := by
    ext z
    refine Subtype.ext (Prod.ext rfl ?_)
    exact Category.assoc _ _ _

def crPull {Y Y' : SmV k} (u : Y'.X ⟶ Y.X) (hu : u ≫ Y.q = Y'.q) :
    GlobalTheory.LogCris.Mor ((schFn Y.q).cr b ht κ) ((schFn Y'.q).cr b ht κ) (RingHom.id b.R) :=
  crMor (RingHom.id b.R) rfl ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩ (schPt b κ u hu) (fun _ _ _ => rfl)

def pull {Y Y' : SmV k} (u : Y'.X ⟶ Y.X) (hu : u ≫ Y.q = Y'.q) (n : ℕ) : Hc b ht κ Y n →ₗ[b.R] Hc b ht κ Y' n :=
  (omMor (crPull b ht κ u hu) (RingHom.id b.R) (fun _ => rfl)).pull n

end CompanionTheory.KM.G4
