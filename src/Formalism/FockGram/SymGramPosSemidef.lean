import Formalism.FockGram.StatementFock
import Formalism.FockGram.FockGramProofs.SubIndexNorm
import Formalism.FockGram.FockGramProofs.CovolGram
import Formalism.FockGram.FockGramProofs.HermDualOf
import Formalism.FockGram.StatementLat
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive

namespace Formalism.E

theorem subIndexNorm : SubIndexNorm := indexEqNormDet

theorem hermDual : HermDual := hermDual_of subIndexNorm

end Formalism.E
