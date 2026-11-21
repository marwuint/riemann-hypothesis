import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

namespace DefFam

variable {T T' J : Type} (F : DefFam K G Pl0 T J)

def comap (f : T' → T) (μ0' : T') : DefFam K G Pl0 T' J where
  v0 := F.v0
  μ0 := μ0'
  X := F.X
  R t := F.R (f t)
  L j t := F.L j (f t)
  tr := F.tr

end DefFam

namespace DefFam3

variable {I0 Ty T T' J : Type} (F3 : DefFam3 K G Pl0 I0 Ty T J)

def comap (f : T' → T) (μ0' : T') : DefFam3 K G Pl0 I0 Ty T' J where
  F := F3.F.comap f μ0'
  RI t := F3.RI (f t)
  LI j t := F3.LI j (f t)
  trI := F3.trI

end DefFam3

namespace FamIn

variable {T T' : Type} {m : ℕ} (A : FamIn K G Pl0 T m)

def comap (f : T' → T) (μ0' : T') : FamIn K G Pl0 T' m where
  v0 := A.v0
  μ0 := μ0'
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j τ := A.muVal j (f τ)
  etaVal := A.etaVal
  ok τ := A.ok (f τ)
  MtildeCSD τ := A.MtildeCSD (f τ)
  leftGroupActionRight τ := A.leftGroupActionRight (f τ)
  heckeR τ := A.heckeR (f τ)
  MtCSD j τ := A.MtCSD j (f τ)
  leftGroupActionLift j τ := A.leftGroupActionLift j (f τ)
  heckeL j τ := A.heckeL j (f τ)

theorem fam_comap (f : T' → T) (μ0' : T') : (A.comap f μ0').fam = A.fam.comap f μ0' := rfl

end FamIn

namespace FamIn3

variable {I0 Ty T T' : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m)

def comap (f : T' → T) (μ0' : T') : FamIn3 K G Pl0 I0 Ty T' m where
  A := A3.A.comap f μ0'
  okI τ := A3.okI (f τ)
  heckeRI τ := A3.heckeRI (f τ)
  heckeLI j τ := A3.heckeLI j (f τ)
  trI := A3.trI

theorem family_inputs_comap_eq (f : T' → T) (μ0' : T') : (A3.comap f μ0').fam3 = A3.fam3.comap f μ0' := rfl

end FamIn3

end Gen

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)

def TupF.incl {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : TupF TU → TupF TC :=
  fun τ => ⟨τ.1, τ.2.imp id fun hm => h hm⟩

theorem TupF.incl_val {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) (τ : TupF TU) : (TupF.incl h τ).1 = τ.1 := rfl

theorem TupF.incl_mu0F {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : TupF.incl h (mu0F TU) = mu0F TC := rfl

variable (v0 : InfinitePlace X.K) {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC)
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)

theorem colIn_comap :
    colIn W Ch sel hX v0 TU Xg S0 xiVal = (colIn W Ch sel hX v0 TC Xg S0 xiVal).comap (TupF.incl h) (mu0F TU) := rfl

theorem colIn3_comap :
    colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv =
      (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).comap (TupF.incl h) (mu0F TU) := rfl

theorem colFam3_comap :
    colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv =
      (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).comap (TupF.incl h) (mu0F TU) := rfl

theorem column_family_base_tuple_comap :
    TupF.incl h (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.μ0 = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.μ0 := rfl

theorem colFam3_R_comap (t : TupF TU) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.R t = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.R (TupF.incl h t) := rfl

theorem colFam3_L_comap (j : Fin R.m) (t : TupF TU) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.L j t =
      (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.L j (TupF.incl h t) := rfl

theorem colFam3_tr_comap :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.tr = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.tr := rfl

theorem colIn3_ok_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.ok t = (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.ok (TupF.incl h t) := rfl

theorem colIn3_muVal_comap (j : Fin R.m) (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.muVal j t =
      (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.muVal j (TupF.incl h t) := rfl

theorem colIn3_okI_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).okI t = (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).okI (TupF.incl h t) := rfl

theorem colIn3_heckeRI_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeRI t =
      (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).heckeRI (TupF.incl h t) := rfl

theorem colIn3_heckeLI_comap (j : Fin R.m) (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeLI j t =
      (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).heckeLI j (TupF.incl h t) := rfl

theorem colIn3_trI_comap :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).trI = (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).trI := rfl

theorem colFam_comap :
    colFam W Ch sel hX v0 TU Xg S0 xiVal = (colFam W Ch sel hX v0 TC Xg S0 xiVal).comap (TupF.incl h) (mu0F TU) := rfl

theorem colFam3_ix_comap :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).base3.Ix = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).base3.Ix := rfl

def colSubRes3 (Zs : DefSub (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).amb3) :
    DefSub (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).amb3 :=
  ⟨fun t => Zs.Z (TupF.incl h t), fun j t => Zs.Zl j (TupF.incl h t)⟩

variable (Zs : DefSub (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).amb3)

theorem colFam3_sameTypes3_restrict_iff (P : Subgroup (Col.G0 X.E Pr.vGs R.r)) (ψ : P →* X.Kˣ) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).SameTypes3 P ψ (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs) ↔
      (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).SameTypes3 P ψ Zs := by
  exact Iff.rfl

end Inst

end Formalism.L2.DIV
