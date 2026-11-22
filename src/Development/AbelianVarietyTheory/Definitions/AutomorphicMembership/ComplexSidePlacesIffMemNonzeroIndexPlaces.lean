import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoIff
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OrZeroOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictedCharacterDataValid
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InclUInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DefiniteSideNonzeroIndexPlacesAnyColumnsScale
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoGeoScalIff

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

set_option maxHeartbeats 2000000 in

def restrict (hH : Holds z.R z.F) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := z.resR h
  cG := z.cG
  geo := z.resGeo h
  pins := z.pins_resR h hc hH.aux.ex hH.prim.thmB
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

set_option maxHeartbeats 2000000 in

theorem inGeo_resGeo_iff (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.InGeo (z.resGeo h) ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  Res.inGeo_iff (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') (g := z.geo)

variable (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ)

theorem mem_nonzero_index_places_iff_at_place_or_conjugate (w : X.B.places.Pl) :
    w ∈ z.W1 F0 ↔ ∃ j, NzAt z.R z.F F0 j (plB X w) ∨ NzAt z.R z.F F0 j (Formalism.DivisionValues.conjPl (plB X w)) := by
  refine exists_congr fun j => ⟨?_, ?_⟩
  · rintro ⟨w', rfl | rfl, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩

theorem nonzero_index_places_conj_stable : ConjStable X (z.W1 F0) := by
  intro w hw
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate] at hw ⊢
  rw [plB_conj, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  exact hw.imp fun _ h => h.symm

set_option maxHeartbeats 2000000 in

theorem nzAt_resR (h : Wt' ⊆ Wt) (j : Fin X.toD7.R.m) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    NzAt (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) F0 j v ↔ NzAt z.R (face0 X I hX (usedOf I T Wt) z.Xg z.tr) F0 j v := by
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels, columnChoiceReferenceFace_eq_bareFaceTwoLevels]
  exact nzAt_res (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') (lev0 I) (chr0 I) (lev1 I) (chr1 I) F0 j v

theorem complex_side_places_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (N : IndefNum (famR X I hX (usedOf I T Wt) z.Xg z.tr).fam3.base3) (hN : N.F0 = F0)
    (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr N (X.toD7.plEq w) ↔ w ∈ z.W1 F0 := by
  subst hN
  exact (complexSide_nonzeroIndexPlaces_iff z.R z.F kap lam err Dc Sp Zsc N (plB X w)).trans (z.mem_nonzero_index_places_iff_at_place_or_conjugate N.F0 w).symm

theorem complex_side_face_numbers_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0) (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
      (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) (X.toD7.plEq w) ↔ w ∈ z.W1 F0 :=
  z.complex_side_places_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc _ ((complexSide_numberContents_eq_scaleAtSubspaces z.R z.F kap lam err Dc Sp Zsc C CH).trans hZ) w

theorem twisted_places_eq_complex_side_of_eq_nonzero_index (hW : z.W1 F0 = Wt) (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0)
    (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    v ∈ ((z.R.updS kap lam).withErr err).twPl ↔
      (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
        (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) v := by
  obtain ⟨w, rfl⟩ := (plB X).surjective v
  exact (z.plB_mem_twPl w).trans ((Set.ext_iff.1 hW w).symm.trans (z.complex_side_face_numbers_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc C CH hZ w).symm)

section Ex

variable (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')

end Ex

end Dat

end Record

end GlobalTheory.Mem.R3

end
