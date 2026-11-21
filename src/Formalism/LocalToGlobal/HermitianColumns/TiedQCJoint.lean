import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianColumns.TiedQC

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwChJoint {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ)
    (H : HermCols D) : Prop where
  Uloc_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    (T.lev u μ i h1 hm β).Uloc v = (H.lev u i h1 hm).Uloc v
  Lb_off : ∀ u μ i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∉ T.Q μ →
    locL v (T.lev u μ i h1 hm β).Lb = locL v (H.lev u i h1 hm).Lb
  Q_off : ∀ u μ, ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal

def clsCast (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.cls i ≃ (D.chTw u D.what₂.mu0).cls i :=
  Equiv.cast (congrArg (fun C => C.cls i) (D.memberColumns_twistedChain_base u).symm)

def yCast (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.Y i ≃ (D.chTw u D.what₂.mu0).Y i :=
  Equiv.cast (congrArg (fun C => C.Y i) (D.memberColumns_twistedChain_base u).symm)

structure TwChMu0 {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ) : Prop where
  eY : ∀ u i hi, T.eY u D.what₂.mu0 i hi = yCast D u i
  eCls0 : ∀ u, T.eCls0 u D.what₂.mu0 = clsCast D u 0

end Formalism.L2.Herm

end
