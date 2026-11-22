import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExtProof
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ImportsAlt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.InvBuild
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchy

namespace ReciprocityTheory.ChartRestriction.G.I2

theorem gSup_holds : GSupStatement := gSup Ext.all.1

theorem dim_holds : DimStatement := dim

theorem split_holds : SplitStatement := split Ext.all

theorem T_holds : TStatement := tOf Ext.all split_holds gSup_holds dim_holds

end ReciprocityTheory.ChartRestriction.G.I2
