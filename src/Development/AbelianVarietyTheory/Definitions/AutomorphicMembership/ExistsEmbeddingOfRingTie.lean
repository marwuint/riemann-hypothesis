import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TieEmbeddingCastLevelTie
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieAll
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieFin
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsiC
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.BlockRationalityField
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BlockRatReal
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddCharIsIntegral

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack.Test

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

section Reduction

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem block_rational : Formalism.L2.G.BlockRationalityField := by
  intro p O Kf _ _ _ _ _ P Tau _ n LL _ h pos G M embLL lam hW hM
  exact blockRatReal P.lam0 h pos G M embLL (fun τ => (lam τ).w) (fun τ => (lam τ).anti) hW hM

variable (D : D7) (sc : Scale)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
  (H0 : Formalism.L2.Herm.Herm0 (recC D sc 1 Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
  (T : ∀ u : D.what₂.Word, Forms0 (recC D sc 1 Lc I ψ hd) u)
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc 1 Lc I ψ hd) B)
  (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
  (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
  (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
  (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
    lamV (lam u w hg) (D.what₂.embLL z))
  (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))

set_option maxHeartbeats 32000000 in
include hK hPos in

theorem comparison_statements (hJ : ∀ u, Joint0 H0.lev0 u (T u))
    (h0 : ∀ u, LevelZeroCharacterRational (D := recC D sc 1 Lc I ψ hd) T u)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        ((cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB).embW u w hg) (ψ u w hg)) :
    CmpHyp0P T (gatTiesC D sc 1 Lc I ψ hd) (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) := by
  have hpos := fun u w hg v s x => pos_C D sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hs : ∀ u, SameUloc (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u :=
    fun u => sameUloc_of_joint (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u (hJ u)
  have N : CmpLeft D sc 1 Lc I ψ hd H0 hL T B hBs hB :=
    { same := hs
      blk := fun u w hg => blkRatRec_of_stmt block_rational _ _ u w hg B
      psi0 := h0
      chi := chi_C D sc 1 Lc I ψ hd H0 hL T B hBs hB hψ
      valInt := valIntRec_of weylLatticeDescent_holds
        (fun u w hg => ex_C_blk D sc 1 Lc I ψ hd H0 hL T B hBs hB u (hs u) w hg
          (blkRatRec_of_stmt block_rational _ _ u w hg B) (h0 u))
        (fun u w hg => frac_of_gatIs _ u w hg (gatIs_recC D sc 1 Lc I ψ hd H0 hL
          (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg))
        (restExB _)
        (restLatO_of hpos (restLatW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) (fun u => hJ u))
          (restGramW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB)))
        (restChi_of (D := recC D sc 1 Lc I ψ hd) T h0) }
  exact N.toHyp0P hpos

end Reduction

end GlobalTheory.Mem.LocalPack.Test
