import Formalism.FormalGroupWitt.Statement
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CongrV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FrobSqV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.WittTeichmullerRoot

namespace Formalism.FG

universe u v w

theorem funEqHomV : FunEqHomV.{u, v, w} := functional_equation_hom_vector

end Formalism.FG
