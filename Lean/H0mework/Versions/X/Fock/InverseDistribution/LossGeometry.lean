import H0mework.Versions.X.Fock.InverseDistribution.InverseDistribution.Consumer
import H0mework.Versions.X.Fock.HistoryConditional.GWordInverseResidual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionLoss

open SourceCopyTimeModel
noncomputable section

theorem norm_sub_axes (value : SourceJointClockGraph.Carrier) :
    ‖value - SourceCopyGraph.axes (mass value) (SourceJointClockGraph.clock value)‖ ^ 2 = ‖hilbert value‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change (‖hilbert value - 0‖ ^ 2 + ‖mass value - mass value‖ ^ 2) +
    ‖SourceJointClockGraph.clock value - SourceJointClockGraph.clock value‖ ^ 2 = _
  simp only [sub_zero, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

end
end SourceInverseDistributionLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
