import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTripleLoc
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (IsInertAt)

namespace PT

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

local instance charZeroFv (v : Pl F) : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective

local instance invTwoFv (v : Pl F) : Invertible (2 : Fv F v) := invertibleOfNonzero two_ne_zero

local instance modTopEv (v : Pl F) : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩

section Pair

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W} {v : Pl F}
  {ψv : AddChar (Fv F v) ℂ} {dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) (locM X.J v) (locM W.J v)) (Fin n × Fin d)}
  {χXv χWv : (Ev E v)ˣ →* Circle} {omv : UG (cV σ v) (locM X.J v) × UG (cV σ v) (locM W.J v) →* Module.End ℂ (Fn F n d v)}
  (L : IsLocPair M ψ χX χW om v ψv dv χXv χWv omv)
include L

theorem actsW {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) {hv : UG (cV σ v) (locM W.J v)}
    (e : (mat h).map (compFin F E v) = hv.1.1) {φ} (hφ : φ ∈ SB _) (φ₁) :
    Acts (evFin F v) (om (1, h)) φ φ₁ ↔ φ₁ = omv.comp (MonoidHom.inr _ _) hv φ := by
  obtain ⟨g', h', e1, e2, H⟩ := L.loc 1 (one_mem_UAt X v) h hh
  obtain rfl : g' = 1 := Subtype.ext (Units.ext (e1.symm.trans (Matrix.map_one _ (map_zero _) (map_one _))))
  obtain rfl : h' = hv := Subtype.ext (Units.ext (e2.symm.trans e))
  exact H φ hφ φ₁

theorem actsX {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) {gv : UG (cV σ v) (locM X.J v)}
    (e : (mat g).map (compFin F E v) = gv.1.1) {φ} (hφ : φ ∈ SB _) (φ₁) :
    Acts (evFin F v) (om (g, 1)) φ φ₁ ↔ φ₁ = omv.comp (MonoidHom.inl _ _) gv φ := by
  obtain ⟨g', h', e1, e2, H⟩ := L.loc g hg 1 (one_mem_UAt W v)
  obtain rfl : h' = 1 := Subtype.ext (Units.ext (e2.symm.trans (Matrix.map_one _ (map_zero _) (map_one _))))
  obtain rfl : g' = gv := Subtype.ext (Units.ext (e1.symm.trans e))
  exact H φ hφ φ₁

theorem exW {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    ∃ hv : UG (cV σ v) (locM W.J v), (mat h).map (compFin F E v) = hv.1.1 := by
  obtain ⟨-, h', -, e2, -⟩ := L.loc 1 (one_mem_UAt X v) h hh
  exact ⟨h', e2⟩

theorem isEv_of {m : ℕ} {Cy : Matrix (Fin d) (Fin m) (AE F E)} (hC : At (evFin F v) Cy) {l : Fn F n d v →ₗ[ℂ] ℂ}
    (hl : IsEvAt M ψ v Cy l) (h0 : ∃ φ ∈ SB _, l φ ≠ 0) : IsEv (cV σ v) ψv dv (Cy.map (compFin F E v)) l := by
  refine ⟨h0, fun z φ hφ => ?_⟩
  have e : (z.map (ThKH.Iwas.sgE E v) * Cyᵀ).map (compFin F E v) = z * (Cy.map (compFin F E v))ᵀ := by
    rw [Matrix.map_mul, Matrix.transpose_map]
    congr 1
    exact Matrix.ext fun i j => ThKH.Iwas.comp_sgE _
  rw [← e]
  exact hl _ φ hφ _ (L.Heisenberg₂ _ (ThKH.Iwas.at_mul_right _ (ThKH.Iwas.at_transpose hC)) φ hφ)

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {v : Pl F}
  {w : HeightOneSpectrum (𝓞 E)}

end PT

end PositivityTheory.ThK
