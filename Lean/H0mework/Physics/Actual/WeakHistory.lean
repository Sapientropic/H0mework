import H0mework.Physics.Actual.HistoryConfiguration
import H0mework.Physics.Actual.FieldsCompactEnumeration
import Mathlib.Topology.MetricSpace.PiNat

/-! The full registered configuration history is read in one countable
Hilbert inventory containing every compact scale and all nine fields. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Weak

noncomputable section

abbrev Payload := ℕ → Fields.CompactL2

instance payloadMetricSpace : MetricSpace Payload := PiCountable.metricSpace

def sequence (index : ℕ) : Payload :=
  Fields.compactCoordinates (History.configuration index)
    (History.configuration_smooth index)

end
end SaturationMonoid.PhysicsCore.Stage9CU.Weak
