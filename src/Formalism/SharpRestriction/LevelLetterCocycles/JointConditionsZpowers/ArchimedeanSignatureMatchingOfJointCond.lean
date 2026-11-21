import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem card_rootsBar (a : (ZMod g)[X]) : Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits (a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))),
    Polynomial.natDegree_map]

theorem rootsBar_frob (a : (ZMod g)[X]) :
    (Formalism.CyclotomicNorms.rootsBar a).map (fun x => x ^ g) = Formalism.CyclotomicNorms.rootsBar a := by
  unfold Formalism.CyclotomicNorms.rootsBar
  have hbij : Function.Bijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) := PerfectRing.bijective_frobenius
  let F : Formalism.CyclotomicNorms.Fbar g ≃+* Formalism.CyclotomicNorms.Fbar g := RingEquiv.ofBijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) hbij
  have h1 : ((a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))).map (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) =
      a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) := by
    rw [Polynomial.map_map]
    congr 1
    ext c
    show (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ g = _
    rw [← map_pow, ZMod.pow_card]
  have h2 := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) (f := (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) F.injective
    (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _))
  rw [h1] at h2
  exact h2

end Roots

end Formalism.MainNotions.N
