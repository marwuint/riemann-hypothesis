import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpper
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockHomeomorph
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLeviStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleDeterminantTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationTransportEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BernsteinZelevinskyGeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationBlockCounts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetBlockMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIntersectionConjugate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellLeviTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCompContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquiv
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoAssembly

def equivComp {G H V V' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : ρ.Equiv ρ') (ψ : H →* G) : Representation.Equiv (ρ.comp ψ) (ρ'.comp ψ) :=
  Representation.Equiv.mk' ⟨e.toLinearEquiv.toLinearMap, fun h => by
      ext x; exact LinearMap.congr_fun (e.isIntertwining' (ψ h)) x⟩ e.invFun
    e.left_inv e.right_inv

set_option maxHeartbeats 1000000 in

theorem jacquetOfInducedFiltration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := by
  intro k _ _ _ _ α β n _ _ _ _ _ _ m _ _ m' _ _ e e'
  let N := Fintype.card n
  let ι : n ≃ Fin N := Fintype.equivFin n
  let E := e.trans ι
  let E' := e'.trans ι
  obtain ⟨βF, hβ⟩ := _root_.GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk m E
  obtain ⟨γF, hγ⟩ := _root_.GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk m' E'
  obtain ⟨φ, hφ, -, hφsc⟩ := _root_.GlobalTheory.CompanionTheory.LeviIso.leviEquiv k E βF hβ
  obtain ⟨φ', hφ', -, -⟩ := _root_.GlobalTheory.CompanionTheory.LeviIso.leviEquiv k E' γF hγ
  obtain ⟨K, w, hcov, hfilt⟩ := _root_.GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform k N βF γF
  let sz : Equiv.Perm (Fin N) → α → β → ℕ := fun v i j =>
    (Finset.univ.filter fun x : Fin N => blk E x = i ∧ blk E' (v.symm x) = j).card
  let toSM : Fin K → SizeMatrix m m' := fun t => ⟨sz (w t), _root_.GlobalTheory.CompanionTheory.CellSizes.sizes_sum E E' (w t)⟩
  have hsz : ∀ v v' : Equiv.Perm (Fin N), permGL k v' ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) ↔ sz v = sz v' := by
    intro v v'
    rw [_root_.GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card k E βF hβ E' γF hγ v v']
    exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => congrFun (congrFun h i) j⟩
  have hself : ∀ v : Equiv.Perm (Fin N), permGL k v ∈ doubleCoset (permGL k v)
      (blockUpper k N βF : Set (GL (Fin N) k)) (blockUpper k N γF) := fun v =>
    (hsz v v).2 rfl
  have inj : Function.Injective toSM := by
    intro t t' h
    have h1 : sz (w t) = sz (w t') := congrArg Subtype.val h
    obtain ⟨j, -, huniq⟩ := hcov (permGL k (w t'))
    exact (huniq t ((hsz _ _).2 h1)).trans (huniq t' (hself _)).symm
  have surj : Function.Surjective toSM := by
    intro B
    obtain ⟨v, hv⟩ := _root_.GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes E E' B
    obtain ⟨t, ht, -⟩ := hcov (permGL k v)
    refine ⟨t, Subtype.ext ?_⟩
    show sz (w t) = B.1
    rw [(hsz _ _).1 ht]
    exact funext fun i => funext fun j => hv i j
  refine ⟨K, Equiv.ofBijective toSM ⟨inj, surj⟩, ?_⟩
  intro W _ _ ρ hρ
  let σ := ρ.comp φ.symm.toMonoidHom
  have hσ : GroundTheory.Automorphic.IsSmooth σ := GlobalTheory.T.isSmooth_comp_continuous φ.symm.toMonoidHom hφsc ρ hρ
  have hF := hfilt W σ hσ
  obtain ⟨V, hF⟩ := hF
  obtain ⟨hV0, hF⟩ := hF
  obtain ⟨hVK, hF⟩ := hF
  obtain ⟨hVmono, hV, hΨ⟩ := hF
  have e1' := _root_.GlobalTheory.CompanionTheory.ParIndReindex.jac_parInd_reindex k e e' ι ρ
  obtain ⟨e1⟩ := e1'
  have e2' := GlobalTheory.T.jac_equiv_jacquetRep_comp_levi_equiv k E' γF hγ φ' hφ' (V := IndSp E ρ) (parInd E ρ)
  obtain ⟨e2⟩ := e2'
  have e3' := _root_.GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd k E βF hβ φ hφ ρ
  obtain ⟨e3⟩ := e3'
  have e4' := _root_.GlobalTheory.CompanionTheory.JacquetEquiv.nonempty_jacquetRep_equiv k N γF (V := IndSp E ρ) (parInd E ρ) _ e3
  obtain ⟨e4⟩ := e4'
  have e12 := e1.trans e2
  have e45 := equivComp e4 φ'.toMonoidHom
  have e5 := e12.trans e45
  have hT := _root_.GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration φ'.toMonoidHom _ _ e5 K _
    (fun j => indRep (cellLeviSub k βF γF (w j)) (normInducing σ γF (w j))) V hV0 hVK hVmono hV hΨ
  obtain ⟨S, hT⟩ := hT
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hT
  refine ⟨S, hS1, hS2, hS3, fun t f g => ?_⟩
  have q1' := hS4 t
  obtain ⟨q1⟩ := q1'
  have c' := _root_.GlobalTheory.CompanionTheory.GeomCell.cell_iso k E βF hβ φ hφ E' γF hγ φ' hφ' ρ (w t)
  obtain ⟨f0, g0, c'⟩ := c'
  obtain ⟨q2⟩ := c'
  have q3' := _root_.GlobalTheory.CompanionTheory.CellCongr.cellFunctor_congr (fun i j => by rw [Fintype.card_fin, Fintype.card_fin]; rfl) f0 g0 f g ρ
  obtain ⟨q3⟩ := q3'
  exact ⟨q1.trans (q2.trans q3)⟩

end GlobalTheory.CompanionTheory.GeoAssembly
