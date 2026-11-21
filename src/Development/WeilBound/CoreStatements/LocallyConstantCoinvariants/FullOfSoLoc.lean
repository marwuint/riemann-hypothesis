import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ContinuousFinId
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.KCo

section Local

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def augF (n d : ℕ) (ν α : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Φ, Full Φ ∧ z = omB ν α g 1 Φ - Φ}

theorem augF_le {ν α : kˣ →* ℂˣ} : augF n d ν α ≤ aug n d ν α :=
  Submodule.span_mono fun _ ⟨g, Φ, h, e⟩ => ⟨g, Φ, h.1, e⟩

end Local

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem full_of_soLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (h : IsCMExt F E σ) (hψ : IsStd ψ)
    (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι} (hι : M.IsLinBar ψ t 1 1 ι) {φ} (hφ : φ ∈ M.SoLoc ψ t) :
    ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → ι φ Y = 0 := by
  obtain ⟨h1, ι', hι', h2⟩ := hφ
  intro Y hY
  obtain ⟨x, hx, h0, rfl⟩ := exists_coB (X := X) (W := W) h t hX hW Y
  exact eigen_kill M h hψ hX hW hι' ((LinearMap.proj (coB σ X W t x)).comp ι) hx h0
    (fun u hu hu1 φ' h' => mult' M hψ hι hu hu1 hx h0 h') h1 (h2 _ hY)

end PositivityTheory.KCo
