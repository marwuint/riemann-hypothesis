import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem wop_sub_mem {F B J : Type*} [Field F] [CommRing B] [Algebra F B] (I : Ideal B)
    (T : J → B) (θ : J → F) (h : ∀ j, T j - algebraMap F B (θ j) ∈ I) (s : List J →₀ F) :
    wop T s - algebraMap F B (wop θ s) ∈ I := by
  rw [← Ideal.Quotient.eq]
  have hT : (fun j => Ideal.Quotient.mkₐ F I (T j)) =
      fun j => ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (θ j) := by
    funext j
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (h j)
  calc Ideal.Quotient.mk I (wop T s) = Ideal.Quotient.mkₐ F I (wop T s) := rfl
    _ = wop (fun j => Ideal.Quotient.mkₐ F I (T j)) s := map_wop _ _ _
    _ = wop (fun j => ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (θ j)) s := by rw [hT]
    _ = ((Ideal.Quotient.mkₐ F I).comp (Algebra.ofId F B)) (wop θ s) := (map_wop _ _ _).symm
    _ = Ideal.Quotient.mk I (algebraMap F B (wop θ s)) := rfl

end UpperTheory.Gal.CertificateRingHomMap

