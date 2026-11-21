import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section Generic

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R]

def latIn (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) : Submodule (𝓞 K) R :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_latIn (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (f : R) :
    f ∈ latIn C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f := by
  unfold latIn latOf
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F.2, hF⟩
  · rintro ⟨hC, hv⟩
    exact ⟨⟨f, hC⟩, hv, rfl⟩

end Generic

variable {D : D7}

abbrev cuspW (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.cuspA j (wtA w) w.n

def supLat (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule (𝓞 T.Q.c.F) (T.R j) :=
  latIn (cuspW T j w) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) isVal_valSet

def FullAt (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Prop :=
  (supLat T j w).FG ∧ Submodule.span T.Q.c.F (supLat T j w : Set (T.R j)) = cuspW T j w

structure Pinned (T : Core D) : Prop where
  pins : T.Q.Pins
  half : (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal) ∧
    T.Q.l.Mb = ∏ k, (T.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))
  evalWD : ∀ j, InR D j →
    EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
  unf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ)
  unTest : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k x,
    FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) ((T.U j σ).un k x)

end GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation
