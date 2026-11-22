import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayContainment

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjI (H : Host E) (I : Ideal (𝓞 E)) : Ideal (𝓞 E) := I.map (H.bar : 𝓞 E →+* 𝓞 E)

def modulus (H : Host E) (Q : Finset (Ideal (𝓞 E))) : Ideal (𝓞 E) := ∏ P ∈ Q, P * conjI H P

variable {H : Host E} {Dw : Datum H} {l : Level H}

def indexIdeal (D : Datum H) (N : Submodule (𝓞 E) D.La) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ (ω : D.La [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] 𝓞 E) (x : Fin (D.p + D.q) → D.La),
    (∀ i, x i ∈ N) ∧ a = ω x}

def DetIdeal (D D' : Datum H) (l₂ : Level H) (t : D.La →ₗ[𝓞 E] D'.La) (𝔣 𝔠 : Ideal (𝓞 E)) : Prop :=
  𝔠 ≠ ⊥ ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∃ (n : ℕ) (ψ : D'.La →ₗ[𝓞 E] D.La),
    0 < n ∧ Nat.Coprime n l₂.M ∧
    (∀ x y, D.EF (ψ x) (ψ y) = (n : ℤ) ^ 2 * D'.EF x y) ∧
    (∀ a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 E) D.La), D.ModN l₂.M (ψ (t a) - n • a)) ∧
    indexIdeal D (LinearMap.range ψ) * conjI H 𝔠 = Ideal.span {(n : 𝓞 E) ^ (D.p + D.q)} * 𝔠

variable {Xo : Moduli Dw l} {c : Coeff l}

def IsCover {n : ℕ} (d : DeltaDat Xo c n) (N : ℕ) (I : Ideal (𝓞 E)) : Prop :=
  d.pd = N ∧ d.I = I ∧ d.l₂.M = l.M * N ∧ d.l₂.Mb = l.Mb * I ∧ d.l₂.A = l.A ∧
  (∃ jK : KA l →+* KA d.l₂, (∀ x, ((jK x : KA d.l₂) : ℂ) = ((x : KA l) : ℂ)) ∧
    d.r ≫ Xo.s = d.Xo₂.s ≫ spMap jK) ∧
  d.EtaOK ∧
  (∃ rF : d.Xo₂.XF d.c₂ ⟶ Xo.XF c,
    rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d.r ∧
    rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion d.hF.ge).toRingHom ∧
    IsFinite rF ∧ Etale rF ∧ Surjective rF) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ y : FrPt Xo c k, ∃ y₂ : FrPt d.Xo₂ d.c₂ k, FrOver d y₂ y

end GlobalTheory.IndefiniteRowSideFullHecke.RayContainment
