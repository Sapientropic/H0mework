import Mathlib.Analysis.ODE.ExistUnique

set_option autoImplicit false

namespace LAlanineTrueFlowDifferential

abbrev Space := Fin 3 → ℝ
abbrev Time := Set.Icc (-(1 / 2) : ℝ) (1 / 2)
abbrev Path := C(Time, Space)

instance time_nonempty : Nonempty Time := ⟨⟨0, by constructor <;> norm_num⟩⟩

def zeroTime : Time := ⟨0, by constructor <;> norm_num⟩

end LAlanineTrueFlowDifferential
