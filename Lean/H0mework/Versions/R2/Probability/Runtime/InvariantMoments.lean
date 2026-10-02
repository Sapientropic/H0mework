import H0mework.Versions.R2.Probability.Runtime.Boundary
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecificLimits.Basic

/-! The existing field probabilities expose actual source means to weak-limit consumers. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedScalarCofinalTopology.NativeProbability

open MeasureTheory SourceGeneratedRuntimeHistoryProbability Filter Topology
open scoped BoundedContinuousFunction

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

local instance : UniformSpace (Field read) := fieldUniform read
local instance : MeasurableSpace (Field read) := fieldBorel read
local instance : BorelSpace (Field read) := ⟨rfl⟩

def empirical (runtime : LivingRuntimeState process) (bound : Nat) : ProbabilityMeasure (Field read) :=
  ⟨(fieldPMF read runtime bound).toMeasure, inferInstance⟩

theorem empirical_map (runtime : LivingRuntimeState process) (bound : Nat) :
    (empirical read runtime bound).map (fieldAction_measurable read).aemeasurable =
      empirical read runtime.tick.next bound := by
  apply ProbabilityMeasure.toMeasure_injective
  exact fieldMeasure_next read runtime bound

theorem integral_empirical (runtime : LivingRuntimeState process) (bound : Nat)
    (f : Field read →ᵇ ℝ) :
    ∫ value, f value ∂(empirical read runtime bound : Measure (Field read)) =
      mean runtime bound (fun state => f (fieldPoint read state)) := by
  have observed : (fieldPMF read runtime bound).map f =
      observedPMF runtime bound (fun state => f (fieldPoint read state)) :=
    PMF.map_comp (fieldPoint read) (statePMF runtime bound) f
  change (∫ value, f value ∂(fieldPMF read runtime bound).toMeasure) = _
  calc
    _ = ∫ value : ℝ, value ∂((fieldPMF read runtime bound).map f).toMeasure := by
      rw [← PMF.toMeasure_map _ _ f.continuous.measurable]
      exact (integral_map (f := fun value : ℝ => value)
        f.continuous.measurable.aemeasurable aestronglyMeasurable_id).symm
    _ = mean runtime bound (fun state => f (fieldPoint read state)) :=
      congrArg (fun probability : PMF ℝ => ∫ value, value ∂probability.toMeasure) observed

theorem empirical_drift_tendsto_zero (runtime : LivingRuntimeState process)
    (f : Field read →ᵇ ℝ) :
    Tendsto (fun bound =>
      (∫ value, f value ∂(empirical read runtime.tick.next bound : Measure (Field read))) -
        ∫ value, f value ∂(empirical read runtime bound : Measure (Field read)))
      atTop (𝓝 (0 : ℝ)) := by
  simp_rw [integral_empirical]
  have denominator : Tendsto (fun bound : Nat => ((bound + 1 : Nat) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero_norm
    (fun bound => by simpa only [Real.norm_eq_abs] using bounded_field_mean_shift read runtime bound f)
  exact tendsto_const_nhds.div_atTop denominator

end
end SourceGeneratedScalarCofinalTopology.NativeProbability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
