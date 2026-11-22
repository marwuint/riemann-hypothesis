import Formalism.DoubleCosetMeasures.Statement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GLRealOpen

open MeasureTheory Measure Topology Matrix

namespace Formalism.DoubleCosetMeasures.P

namespace GeneralLinearIntegersOpenCompact

section Alg

variable {K : Type} [CommRing K]

noncomputable def glR (R : Subring K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  _root_.UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n

end Alg

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem glR_open (R : Subring K) (hR : IsOpen (R : Set K)) (n : ℕ) :
    IsOpen (glR R n : Set (GL (Fin n) K)) :=
  _root_.UpperTheory.Reformulated.B.GLRealOpen.glR_open R hR n

theorem glR_compact [T2Space K] (R : Subring K) (hR : IsCompact (R : Set K)) (n : ℕ) :
    IsCompact (glR R n : Set (GL (Fin n) K)) := by
  let S : Set (Matrix (Fin n) (Fin n) K) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (R : Set K)))
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hR))
  have hS' : IsCompact (MulOpposite.unop ⁻¹' S : Set (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.isCompact_preimage.mp hS
  have := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  convert this using 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a _ b _ => h1 a b, fun a _ b _ => h2 a b⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b => h1 a (Set.mem_univ _) b (Set.mem_univ _),
      fun a b => h2 a (Set.mem_univ _) b (Set.mem_univ _)⟩

end Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

end GeneralLinearIntegersOpenCompact

open GeneralLinearIntegersOpenCompact

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

end Formalism.DoubleCosetMeasures.P
