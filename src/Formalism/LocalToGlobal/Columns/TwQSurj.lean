import Formalism.LocalToGlobal.Columns.TwQDefs
import Formalism.LocalToGlobal.Columns.MtHeckeKv
import Formalism.LocalToGlobal.Columns.RecLevelCls

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG

section QSurj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

def QIntGL {v : HeightOneSpectrum (𝓞 F)} (k : GL (Fin n) (v.adicCompletion F)) : Prop :=
  (∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, (((k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F)

variable (ST SG) in

def FrLat (q : QLoc hc n Q Θ) : Prop :=
  ∀ (x : UAd hc n) (p : DecoF E n ST SG Q), decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = p.deco → ∀ P : Q,
    QIntGL ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)

end QSurj

end Formalism.L2.Col
