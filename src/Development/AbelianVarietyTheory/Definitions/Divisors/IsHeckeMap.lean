import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def IsHecke (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta (g x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSub o g N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

def IsHeckeMap (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) (F : RepFam b N) (F' : RepFam b (N * k))
    (π : F'.X ⟶ F.X) : Prop :=
  π ≫ F.s = F'.s ∧ ∃ (o' : Obj b N F'.s) (ψ : F'.univ.A ⟶ o'.A), IsHecke g c k N F'.univ o' ψ ∧
    Nonempty (ObjMap o' F.univ π)

theorem IsHecke.dvd {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : Obj b (N * k) s} {o' : Obj b N s}
    {ψ : o.A ⟶ o'.A} (h : IsHecke g c k N o o' ψ) : c ∣ k ^ 2 :=
  h.2.2.2.2.2

theorem IsHecke.pol {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : Obj b (N * k) s} {o' : Obj b N s}
    {ψ : o.A ⟶ o'.A} (h : IsHecke g c k N o o' ψ) :
    Nonempty (LBIso (lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) :=
  h.2.2.2.2.1

theorem IsHecke.eta {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : Obj b (N * k) s} {o' : Obj b N s}
    {ψ : o.A ⟶ o'.A} (h : IsHecke g c k N o o' ψ) (x : D.La) : o'.eta x = o.eta (g x) ≫ ψ :=
  h.2.2.1 x

theorem IsHeckeMap.dvd {g : D.La →ₗ[D.O] D.La} {c k N : ℕ} {F : RepFam b N} {F' : RepFam b (N * k)}
    {π : F'.X ⟶ F.X} (h : IsHeckeMap g c k N F F' π) : c ∣ k ^ 2 := by
  obtain ⟨-, o', ψ, hH, -⟩ := h
  exact IsHecke.dvd hH

end GlobalTheory.UPel.HT.Hecke
