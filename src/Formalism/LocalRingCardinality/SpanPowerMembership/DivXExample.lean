import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

def geoExample (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F where
  Var := Empty
  dim := fun Y => Empty.elim Y
  Fn := fun Y => Empty.elim Y
  fnField := fun Y => Empty.elim Y
  fnAlg := fun Y => Empty.elim Y
  Dv := fun Y => Empty.elim Y
  dvGrp := fun Y => Empty.elim Y
  Eff := fun Y => Empty.elim Y
  eff_zero := fun Y => Empty.elim Y
  eff_add := fun Y => Empty.elim Y
  H0 := fun Y => Empty.elim Y
  degreeZeroCohomology_finiteDimensional := fun Y => Empty.elim Y
  mul_mem_riemannRochSpace_add := fun Y => Empty.elim Y
  riemannRoch_mono := fun Y => Empty.elim Y
  KY := fun Y => Empty.elim Y
  Cl := fun Y => Empty.elim Y
  properCl := fun Y => Empty.elim Y
  subCl := fun Y => Empty.elim Y
  supp := fun Y => Empty.elim Y
  inter := fun Y => Empty.elim Y
  nef := fun Y => Empty.elim Y
  big := fun Y => Empty.elim Y
  bpf := fun Y => Empty.elim Y
  phiBir := fun Y => Empty.elim Y
  phiNoContr := fun Y => Empty.elim Y
  vanishOn := fun Y => Empty.elim Y
  hdim := fun Y => Empty.elim Y
  pts := fun Y => Empty.elim Y
  ptsMeas := fun Y => Empty.elim Y
  vol := fun Y => Empty.elim Y
  FnC := fun Y => Empty.elim Y
  fnCRing := fun Y => Empty.elim Y
  fnCAlg := fun Y => Empty.elim Y
  cx := fun Y => Empty.elim Y
  cx_smul := fun Y => Empty.elim Y
  Met := fun Y => Empty.elim Y
  mAdd := fun Y => Empty.elim Y
  mPow := fun Y => Empty.elim Y
  fsMet := fun Y => Empty.elim Y
  pn := fun Y => Empty.elim Y
  pnK := fun Y => Empty.elim Y
  mSmooth := fun Y => Empty.elim Y
  mPsh := fun Y => Empty.elim Y
  redZero := fun Y => Empty.elim Y
  agreeOn := fun Y => Empty.elim Y
  resNorm := fun Y => Empty.elim Y
  Adl := fun Y => Empty.elim Y
  ofW := fun Y => Empty.elim Y
  twist := fun Y => Empty.elim Y
  arTop := fun Y => Empty.elim Y
  arVol := fun Y => Empty.elim Y
  nefA := fun Y => Empty.elim Y
  supInf := fun Y => Empty.elim Y
  supFin := fun Y => Empty.elim Y
  cutGood := fun Y => Empty.elim Y
  cutHt := fun Y => Empty.elim Y
  cutOrd := fun Y => Empty.elim Y
  resFull := fun Y => Empty.elim Y
  resDeg := fun Y => Empty.elim Y
  supInf_ofW := fun Y => Empty.elim Y
  supInf_twist := fun Y => Empty.elim Y
  supFin_twist := fun Y => Empty.elim Y
  regOn := fun Y => Empty.elim Y

variable (D : D7)

end Formalism.BasicNotions.Examples₂
