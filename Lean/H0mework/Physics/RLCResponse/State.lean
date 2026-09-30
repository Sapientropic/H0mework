import H0mework.Physics.PortCoupling.State
import H0mework.Physics.RLCResponse.Drive

/-!
# Physical initial and total-response port state

A second-order series-RLC row has two independent physical initial data:
capacitor voltage and loop current.  The older dimensioned run state also
stores an auxiliary charge-coordinate used by the damped shear; it is not an
additional independent circuit initial datum.  This carrier therefore records
exactly the physical `(V,I)` state at every finite embodiment channel.
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

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

@[ext] structure FiniteDimensionedSeriesRLCPortState where
  voltageAt : FiniteEmbodimentChannel → SIVolt
  currentAt : FiniteEmbodimentChannel → SIAmpere

end


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
