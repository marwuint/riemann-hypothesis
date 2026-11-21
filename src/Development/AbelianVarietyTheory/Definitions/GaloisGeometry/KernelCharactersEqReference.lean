import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem

noncomputable section

namespace GlobalTheory.KerJ.CharModel

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

section General

variable {L : Type} [Field L] [NumberField L]

theorem prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    { toFun := fun x => x.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨fun w => Units.map (p w) a, ?_⟩
  have h : ((∏ w, infIdele L w (Units.map (p w) a) : Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1) := by
    rw [Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w ((a : AdeleRing (𝓞 L) L).1 w)) = ι (fun w => (a : AdeleRing (𝓞 L) L).1 w)
    rw [← map_prod]
    exact congrArg ι (Finset.univ_prod_mulSingle (fun w : InfinitePlace L => ((a : AdeleRing (𝓞 L) L).1 w : w.Completion)))
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem isFin_finPart (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

theorem isUnitary_of_orderDvd {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) : χ.IsUnitary := fun x => by
  have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
  have h2 : χ.1 x ^ n = 1 := by simpa using h1
  have h3 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3

end General

variable {D : D7} {C : CharFrame D} (Dt : DtTied D C) {nch : NChoice D} (Tp : TupTied D C nch)

theorem eDt_finPart (a : Ideles D.host.E) : Dt.eDt (finPartI D.host.E a) = Dt.eDt a := by
  obtain ⟨y, hy⟩ := prod_inf_mul_finPart a
  conv_rhs => rw [← hy]
  rw [map_mul, map_prod, Finset.prod_eq_one fun w _ => Dt.inf w (y w), one_mul]

end GlobalTheory.KerJ.CharModel
