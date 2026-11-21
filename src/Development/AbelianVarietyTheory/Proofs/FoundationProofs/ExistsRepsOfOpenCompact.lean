import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsObj

open GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting hiding levJ

section Space

variable {D : D7}

theorem gramAt_posDef {V : HSp D} (hp : V.IsPosDef) (hs : V.SigOK) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  have := hs (tauE D τ)
  rw [hp] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem exists_compact_of_fin (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)}
    (hC : IsCompact C) : ∃ K : Set (GA D V), IsCompact K ∧ ∀ k : GA D V, (∀ i j, (finHom V k).1 i j ∈ C) → k ∈ K := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  choose R hR using fun τ => GlobalTheory.DefiniteQuotient.exists_bound_unitary (hV τ)
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k hk => hKe k fun i j => hCe' _ (hk i j) fun τ => ?_⟩
  have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
  have hu : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k) * V.gram.map (incA D) * Formalism.L2.Theta.mt V k = V.gram.map (incA D) := k.2
  have e : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k)).map ((θ τ).comp (infPart D)) =
      ((Formalism.L2.Theta.mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
    ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
  have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
  simp only [Matrix.map_mul, e, hJ] at this
  exact ((hR τ _ this i j).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))

theorem finite_stab (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V))
    {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)} (hC : IsCompact C) (hJ : ∀ k ∈ J, ∀ i j, k.1.1 i j ∈ C) (g : Bridge.Gf V) :
    Finite (Bridge.stab (Bridge.ratF V) J g) := by
  obtain ⟨-, -, h2, -, hg, hd, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_fin V hV hC
  obtain ⟨x, rfl⟩ := (finHom V).rangeRestrict_surjective g
  have hK' : IsCompact ((fun k => x * k * x⁻¹) '' K) := hK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : GQ V → GA D V) ⁻¹' ((fun k => x * k * x⁻¹) '' K)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK').finite_of_discrete
  refine Set.Finite.subset hfin fun γ hγ => ⟨x⁻¹ * γ.1 * x, hKe _ ?_, by group⟩
  have h := hJ _ ((Bridge.mem_stab _).1 hγ)
  rw [map_mul, map_mul, map_inv]
  exact h

theorem exists_cover_of_compact {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) {C : Set G} (hC : IsCompact C)
    (hCe : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) :
    ∃ (m : ℕ) (c : Fin m → H), ∀ g, ∃ (a : Fin m) (γ : Γ) (k : J), g = π.comp Γ.subtype γ * c a * k := by
  obtain ⟨S, -, hS⟩ := hC.elim_nhds_subcover (fun x => {y | π (x⁻¹ * y) ∈ J}) fun x _ =>
    (ho.preimage (continuous_const_mul x⁻¹)).mem_nhds (by simp)
  refine ⟨_, fun a => π (S.equivFin.symm a).1, fun g => ?_⟩
  obtain ⟨x, rfl⟩ := hπ g
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hCe x
  obtain ⟨s, hs, hcs⟩ := Set.mem_iUnion₂.1 (hS hc)
  exact ⟨S.equivFin ⟨s, hs⟩, ⟨γ, hγ⟩, ⟨_, hcs⟩, by simp [mul_assoc]⟩

theorem exists_cover (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V)) (ho : IsOpenLev V J) :
    ∃ (m : ℕ) (c : Fin m → Bridge.Gf V), ∀ g, ∃ (a : Fin m) (γ : GQ V) (k : J), g = Bridge.ratF V γ * c a * k :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  (GlobalTheory.DefiniteQuotient.exists_compact V hV).elim fun _ h =>
    exists_cover_of_compact (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective J ho h.1 h.2

end Space

section Levels

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T)

theorem isPosDef_of_vStd (hV : VStd D i) : (Vc D i).IsPosDef := fun τ => by
  have h := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) τ
  rw [GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hV, if_neg Bool.false_ne_true] at h
  rw [D.sp.V_rank _ (by omega) i.2]
  exact h

end Levels

end GlobalTheory.RepsObj

end
