import H0mework.Versions.R2.Probability.Runtime.InvariantMoments
import H0mework.Versions.R2.Probability.Source.Hilbert
import H0mework.Versions.R2.Probability.Source.Runtime
import Mathlib.MeasureTheory.Function.L2Space

/-! The actual finite-history update generates pullback between its two changing L² spaces. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedEmpiricalHilbert

open SourceGeneratedScalarCofinalTopology.NativeProbability MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)

local instance : MeasurableSpace (Field read) := fieldBorel read

abbrev Space (runtime : LivingRuntimeState process) (bound : Nat) :=
  Lp ℂ 2 (empirical read runtime bound).toMeasure

theorem source_measurePreserving (runtime : LivingRuntimeState process) (bound : Nat) :
    MeasurePreserving (fieldAction read) (empirical read runtime bound).toMeasure
      (empirical read runtime.tick.next bound).toMeasure :=
  by
    rw [SourceOwnedObservationHistory.Runtime.empirical_eq read runtime bound,
      SourceOwnedObservationHistory.Runtime.empirical_eq read runtime.tick.next bound]
    exact SourceOwnedObservationHistory.source_measurePreserving process.successor read runtime.state bound

def pullback (runtime : LivingRuntimeState process) (bound : Nat) :
    Space read runtime.tick.next bound →ₗᵢ[ℂ] Space read runtime bound :=
  Lp.compMeasurePreservingₗᵢ ℂ (fieldAction read) (source_measurePreserving read runtime bound)

theorem pullback_ae (runtime : LivingRuntimeState process) (bound : Nat)
    (value : Space read runtime.tick.next bound) :
    pullback read runtime bound value =ᵐ[(empirical read runtime bound).toMeasure]
      value ∘ fieldAction read :=
  Lp.coeFn_compMeasurePreserving value (source_measurePreserving read runtime bound)

theorem pullback_norm (runtime : LivingRuntimeState process) (bound : Nat)
    (value : Space read runtime.tick.next bound) :
    ‖pullback read runtime bound value‖ = ‖value‖ :=
  (pullback read runtime bound).norm_map value

theorem pullback_inner (runtime : LivingRuntimeState process) (bound : Nat)
    (left right : Space read runtime.tick.next bound) :
    ⟪pullback read runtime bound left, pullback read runtime bound right⟫_ℂ = ⟪left, right⟫_ℂ :=
  (pullback read runtime bound).inner_map_map left right

end
end SourceGeneratedEmpiricalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
