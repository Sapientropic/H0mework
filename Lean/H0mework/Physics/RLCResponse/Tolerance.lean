import H0mework.Physics.RLCResponse.State

/-!
# Typed settling tolerances for a driven RLC port

Voltage and current tolerances remain separately dimensioned.  Their numeric
ratios may be compared only after division by the matching positive SI scale.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Netlist
namespace Dissipative
namespace Dimensioned
namespace Driven
namespace Interface

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

@[ext] structure PositiveDrivenPortTolerance where
  voltageTolerance : SIVolt
  currentTolerance : SIAmpere
  voltageTolerancePositive : 0 < voltageTolerance.value
  currentTolerancePositive : 0 < currentTolerance.value

theorem PositiveDrivenPortTolerance.voltageTolerance_ne
    (tolerance : PositiveDrivenPortTolerance) :
    tolerance.voltageTolerance.value ≠ 0 :=
  ne_of_gt tolerance.voltageTolerancePositive

theorem PositiveDrivenPortTolerance.currentTolerance_ne
    (tolerance : PositiveDrivenPortTolerance) :
    tolerance.currentTolerance.value ≠ 0 :=
  ne_of_gt tolerance.currentTolerancePositive

end Interface
end Driven
end Dimensioned
end Dissipative
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid
