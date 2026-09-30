import H0mework.Versions.Y.Arithmetic.SonineProjection.MeanZero
import H0mework.Versions.Y.Arithmetic.RieszForcing.SourceParity

/-! The fixed actual endpoint columns generate their responses through the original source inverse. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Response

open Complex Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (Measure.restrict (volume : Measure ℝ) (symmetricInterval q))

def eta : BurnolQuarterMeanZeroCarrier := Constructor.endpointColumn q + Constructor.endpointColumn (-q)

def u : BurnolQuarterMeanZeroCarrier := burnolMeanZeroBlockInverse eta

def v : BurnolQuarterMeanZeroCarrier := burnolMeanZeroTruncatedFourier u

theorem u_equation : burnolMeanZeroOneMinusSquare u = eta := by
  change (burnolMeanZeroOneMinusSquare * burnolMeanZeroBlockInverse) eta = eta
  rw [burnolMeanZeroBlockInverse_right]
  rfl

theorem u_source_columns :
    u = burnolMeanZeroBlockInverse (Constructor.endpointColumn q) +
      burnolMeanZeroBlockInverse (Constructor.endpointColumn (-q)) := map_add _ _ _

theorem source_pair_equation : u - burnolMeanZeroTruncatedFourier v =
    Constructor.endpointColumn q + Constructor.endpointColumn (-q) := u_equation

private theorem phase_state_reflection (endpoint : ℝ) :
    reflectRestricted q (Constructor.compact (Constructor.phase endpoint) (Constructor.phaseContinuous endpoint)) =
      Constructor.compact (Constructor.phase (-endpoint)) (Constructor.phaseContinuous (-endpoint)) := by
  let state := Constructor.compact (Constructor.phase endpoint) (Constructor.phaseContinuous endpoint)
  let reflection := negMeasurePreserving_restrict q
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving state reflection,
    reflection.quasiMeasurePreserving.ae (Constructor.compact_read _ (Constructor.phaseContinuous endpoint)),
    Constructor.compact_read _ (Constructor.phaseContinuous (-endpoint))] with x reflected negative direct
  change reflectRestricted q state x = state (-x) at reflected
  rw [reflected, negative, direct]
  simp only [Constructor.phase, mul_neg, neg_mul, neg_neg]

private theorem endpoint_reflection (endpoint : ℝ) :
    reflectRestricted q (Constructor.endpointColumn endpoint : BurnolQuarterIntervalL2) =
      (Constructor.endpointColumn (-endpoint) : BurnolQuarterIntervalL2) := by
  change reflectRestricted q (burnolQuarterMeanZeroProjection _) = burnolQuarterMeanZeroProjection _
  rw [← burnolQuarterMeanZeroProjection_reflect]
  congr 1
  rw [map_sub, map_smul, map_smul, phase_state_reflection,
    ← sourceTruncatedFourier_reflect, reflectRestricted_intervalConstant]

theorem eta_reflection : reflectRestricted q (eta : BurnolQuarterIntervalL2) = eta := by
  change reflectRestricted q ((Constructor.endpointColumn q : BurnolQuarterIntervalL2) +
    (Constructor.endpointColumn (-q) : BurnolQuarterIntervalL2)) = _
  rw [map_add, endpoint_reflection, endpoint_reflection, neg_neg, add_comm]
  rfl

theorem u_reflection : reflectRestricted q (u : BurnolQuarterIntervalL2) = u := by
  have reflected : burnolMeanZeroOneMinusSquare (sourceMeanZeroReflection u) = eta := by
    change sourceMeanZeroReflection u -
      burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier (sourceMeanZeroReflection u)) = eta
    rw [sourceMeanZeroFourier_reflect, sourceMeanZeroFourier_reflect]
    apply Subtype.ext
    change reflectRestricted q (u : BurnolQuarterIntervalL2) -
      reflectRestricted q (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier u) : BurnolQuarterIntervalL2) = _
    rw [← map_sub]
    exact (congrArg (fun state : BurnolQuarterMeanZeroCarrier => reflectRestricted q (state : BurnolQuarterIntervalL2))
      u_equation).trans eta_reflection
  have inverseLeft : burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare = 1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  have recovered := congrArg burnolMeanZeroBlockInverse reflected
  change (burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare) (sourceMeanZeroReflection u) = u at recovered
  rw [inverseLeft] at recovered
  exact congrArg (fun state : BurnolQuarterMeanZeroCarrier => (state : BurnolQuarterIntervalL2)) recovered

theorem v_reflection : reflectRestricted q (v : BurnolQuarterIntervalL2) = v := by
  have fixed : sourceMeanZeroReflection u = u := Subtype.ext u_reflection
  have returned := sourceMeanZeroFourier_reflect u
  rw [fixed] at returned
  exact congrArg (fun state : BurnolQuarterMeanZeroCarrier => (state : BurnolQuarterIntervalL2)) returned.symm

end
end OriginalRieszSource.Response
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
