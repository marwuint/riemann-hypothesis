import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeVariant
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

noncomputable section

open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.IndefR.NX

section GLv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)

abbrev Kv : Subgroup (GL (Fin n) (v.adicCompletion F)) := GLint (Fin n) (Ov F v)

variable {v n} {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]

end GLv

section Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def compV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : GA D V) :
    GL (Fin V.rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
  Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) (Formalism.IndefR.Lev.finE V h)

structure SplitEmb (V : HSp D) (K : Set (GA D V)) where
  Sp : Set (HeightOneSpectrum (𝓞 D.host.F))
  sp : ∀ v ∈ Sp, D.host.E ⊗[D.host.F] v.adicCompletion D.host.F ≃+* v.adicCompletion D.host.F × v.adicCompletion D.host.F
  sp_sig : ∀ v (hv : v ∈ Sp) x, sp v hv (sigR D.sp.cm.sig (v.adicCompletion D.host.F) x) = swapR _ (sp v hv x)
  sp_alg : ∀ v (hv : v ∈ Sp) (a : v.adicCompletion D.host.F), sp v hv ((1 : D.host.E) ⊗ₜ[D.host.F] a) = (a, a)
  emb : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin V.rank) (v.adicCompletion D.host.F) →* GA D V
  emb_fin : ∀ v a, emb v a ∈ GfC V
  emb_at : ∀ v (hv : v ∈ Sp) a, Formalism.UG.bc ((RingHom.fst _ _).comp (sp v hv).toRingHom) (compV V v (emb v a)) = a
  emb_off : ∀ v ∈ Sp, ∀ a, ∀ w, w ≠ v → compV V w (emb v a) = 1
  emb_K : ∀ v, ∀ a ∈ Kv v V.rank, emb v a ∈ K
  emb_comm : ∀ v v', v ≠ v' → ∀ a b, emb v a * emb v' b = emb v' b * emb v a

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

end Concrete

end Formalism.IndefR.NX
