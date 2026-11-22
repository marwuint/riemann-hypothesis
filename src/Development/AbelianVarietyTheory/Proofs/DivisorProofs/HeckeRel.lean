import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

structure IntSim (D : Datum F) (p : ℕ) where
  c : ℕ
  k : ℕ
  c_cop : c.Coprime p
  k_cop : k.Coprime p
  g : ℕ → D.La →ₗ[𝓞 F] D.La
  compat : ∀ n m : ℕ, (n * m).Coprime p → ∀ a, ∃ b, g (n * m) a - g n a = n • b
  sim : ∀ n : ℕ, n.Coprime p → ∃ u : ℤ, IsCoprime u (n : ℤ) ∧
    ∀ a b, (n : ℤ) ∣ D.EF (g n a) (g n b) - c * u * D.EF a b
  onto : ∀ n : ℕ, n.Coprime p → ∀ a, ∃ b d, g n b = k • a + n • d

namespace IntSim

variable {D : Datum F} {p : ℕ}

def ofLinear (g : D.La →ₗ[𝓞 F] D.La) (c k : ℕ) (hc : c.Coprime p) (hk : k.Coprime p)
    (hg : ∀ x y, D.EF (g x) (g y) = c * D.EF x y) (hon : ∀ x, ∃ y, g y = k • x) : IntSim D p where
  c := c
  k := k
  c_cop := hc
  k_cop := hk
  g _ := g
  compat n m _ a := ⟨0, by simp⟩
  sim n _ := ⟨1, isCoprime_one_left, fun a b => by rw [hg]; simp⟩
  onto n _ a := let ⟨y, hy⟩ := hon a; ⟨y, 0, by simp [hy]⟩

def scalar (D : Datum F) (m : ℕ) (hm : m.Coprime p) : IntSim D p :=
  ofLinear (D := D) (m • LinearMap.id) (m ^ 2) m (Nat.Coprime.pow_left 2 hm) hm
    (fun x y => by simp [LinearMap.map_smul_of_tower]; ring) (fun x => ⟨x, by simp⟩)

end IntSim

variable {S : Scheme.{0}}

def HeckeRel {D : Datum F} {p N N' : ℕ} (g : IntSim D p) {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s)
    (o' : Obj D p N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ Etale ψ.left ∧
    (∀ x, o'.eta x = o.eta ((N' / (N * g.k)) • g.g N' x) ≫ ψ) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (t : Over.mk x ⟶ o.A),
      t ≫ ψ = 1 ↔ ∃ a, t = toUnit _ ≫ o.eta ((N' / g.k) • g.g N' a)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → n.Coprime p →
      ∀ (P Q : Over.mk x ⟶ o.A), P ^ n = 1 → Q ^ n = 1 → ∀ ζ : kˣ,
        Out.WeilIs o'.A o'.PP.L n (P ≫ ψ) (Q ≫ ψ) (unitOn ζ) →
          Out.WeilIs o.A o.PP.L ((g.k ^ 2 * n : ℕ) : ℤ) P Q (unitOn (ζ ^ g.c))

def IsHecke {D : Datum F} {p N N' : ℕ} (g : IntSim D p) (M' : IntModel D p N') (M : IntModel D p N)
    (π : M'.X ⟶ M.X) : Prop :=
  π ≫ M.s = M'.s ∧ ∃ (o : Obj D p N M'.s) (ψ : M'.univ.A ⟶ o.A), HeckeRel g M'.univ o ψ ∧ Nonempty (ObjMap o M.univ π)

end GlobalTheory.UPel
