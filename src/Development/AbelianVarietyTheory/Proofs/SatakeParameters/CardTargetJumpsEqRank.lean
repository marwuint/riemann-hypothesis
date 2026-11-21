import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

namespace GlobalTheory.HTW.Model

def WA : WordData 3 where
  up i := i = 1
  sz i := if i = 2 then 3 else 10000
  b := 10000
  w := 3
  S := 1
  η := 1
  m := 1
  J1 i := if i = 1 then {10001, 0} else if i = 2 then {-4, 1} else {-10000, -1}
  J2 i := if i = 1 then {10001, 0} else if i = 2 then {-4} else {-10000, -1}

instance decThickWA : DecidablePred WA.thick := fun i => by unfold WordData.thick; infer_instance

def WB : WordData 2 where
  up i := i = 1
  sz i := if i = 1 then 5 else 100
  b := 100
  w := 5
  S := 1
  η := 1
  m := 1
  J1 i := if i = 1 then {6, 0} else {-100, 1}
  J2 i := if i = 1 then {6, 0} else {-100, -100, 1}

instance decThickWB : DecidablePred WB.thick := fun i => by unfold WordData.thick; infer_instance

end GlobalTheory.HTW.Model
