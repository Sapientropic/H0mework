import H0mework.NavierStokes.ReferenceErrorReferenceBarrier.Moving
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferenceBarrier

open Set Filter MeasureTheory

private theorem first_threshold {f : Real → Real} {a b threshold : Real}
    (continuous : ContinuousOn f (Icc a b)) (initial : f a < threshold)
    (witness : ∃ t ∈ Icc a b, threshold ≤ f t) :
    ∃ hit ∈ Icc a b, f hit = threshold ∧ ∀ t ∈ Icc a hit, f t ≤ threshold := by
  let roots := Icc a b ∩ f ⁻¹' {threshold}
  have compact : IsCompact roots := isCompact_Icc.of_isClosed_subset
    (continuous.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have nonempty : roots.Nonempty := by
    rcases witness with ⟨t, within, reached⟩
    obtain ⟨root, rootWithin, value⟩ := intermediate_value_Icc within.1
      (continuous.mono (Icc_subset_Icc le_rfl within.2)) ⟨initial.le, reached⟩
    exact ⟨root, ⟨⟨rootWithin.1, rootWithin.2.trans within.2⟩, value⟩⟩
  obtain ⟨hit, hitWithin, minimal⟩ := compact.exists_isMinOn nonempty continuousOn_id
  have hitValue : f hit = threshold := hitWithin.2
  refine ⟨hit, hitWithin.1, hitValue, ?_⟩
  intro t within
  by_contra above
  obtain ⟨root, rootWithin, value⟩ := intermediate_value_Icc within.1
    (continuous.mono (Icc_subset_Icc le_rfl (within.2.trans hitWithin.1.2)))
      ⟨initial.le, (not_le.mp above).le⟩
  have rootMember : root ∈ roots := ⟨⟨rootWithin.1, rootWithin.2.trans (within.2.trans hitWithin.1.2)⟩, value⟩
  have hitLe : hit ≤ root := minimal rootMember
  have same : t = hit := le_antisymm within.2 (hitLe.trans rootWithin.2)
  exact above (by rw [same, hitValue])

/-- A source barrier strictly inside the validity threshold closes the local-power
bootstrap. Smallness of the controlled field is generated, not supplied. -/
theorem cubic_local_power_barrier {f power A R barrier derivative : Real → Real} {a b κ threshold : Real}
    (fieldContinuous : ContinuousOn f (Icc a b))
    (rateContinuous : ContinuousOn A (Icc a b)) (inputContinuous : ContinuousOn R (Icc a b))
    (derivativeContinuous : ContinuousOn derivative (Icc a b))
    (barrierDerivative : ∀ t ∈ Icc a b, HasDerivAt barrier (derivative t) t)
    (powerIntegrable : IntervalIntegrable power volume a b)
    (energy : ∀ t ∈ Icc a b, (∫ u in a..t, power u) = f t - f a)
    (localPower : ∀ᵐ t ∂volume.restrict (Icc a b),
      f t ≤ threshold → power t ≤ κ * f t ^ 3 + A t * f t + R t)
    (initial : f a ≤ barrier a) (inside : ∀ t ∈ Icc a b, barrier t < threshold)
    (inward : ∀ t ∈ Icc a b, κ * barrier t ^ 3 + A t * barrier t + R t ≤ derivative t) :
    ∀ t ∈ Icc a b, f t ≤ barrier t := by
  by_cases ordered : a ≤ b
  · have compare (terminal : Real) (within : terminal ∈ Icc a b)
        (small : ∀ t ∈ Icc a terminal, f t ≤ threshold) :
        ∀ t ∈ Icc a terminal, f t ≤ barrier t := by
      have included : Icc a terminal ⊆ Icc a b := Icc_subset_Icc le_rfl within.2
      have localIntegrable : IntervalIntegrable power volume a terminal := powerIntegrable.mono_set (by
        rw [uIcc_of_le within.1, uIcc_of_le ordered]
        exact included)
      have bounded : power ≤ᵐ[volume.restrict (Icc a terminal)] fun t => κ * f t ^ 3 + A t * f t + R t := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset included localPower,
          ae_restrict_mem measurableSet_Icc] with t bound member
        exact bound (small t member)
      have growthContinuous : ContinuousOn (fun t => κ * f t ^ 3 + A t * f t + R t) (Icc a terminal) :=
        ((((fieldContinuous.pow 3).const_mul κ).add (rateContinuous.mul fieldContinuous)).add inputContinuous).mono included
      exact cubic_moving_barrier (fieldContinuous.mono included) (rateContinuous.mono included)
        (inputContinuous.mono included) (derivativeContinuous.mono included)
        (fun t member => barrierDerivative t (included member))
        (increments_of_energy within.1 localIntegrable growthContinuous
          (fun t member => energy t (included member)) bounded) initial
        (fun t member => inward t (included member))
    have small : ∀ t ∈ Icc a b, f t < threshold := by
      intro t within
      by_contra reached
      obtain ⟨hit, hitWithin, hitValue, earlier⟩ := first_threshold fieldContinuous
        (initial.trans_lt (inside a ⟨le_rfl, ordered⟩)) ⟨t, within, not_lt.mp reached⟩
      have bound := compare hit hitWithin earlier hit ⟨hitWithin.1, le_rfl⟩
      have strict := bound.trans_lt (inside hit hitWithin)
      rw [hitValue] at strict
      exact (lt_irrefl threshold) strict
    exact compare b ⟨ordered, le_rfl⟩ (fun t within => (small t within).le)
  · intro t within
    exact False.elim (ordered (within.1.trans within.2))

end SaturationMonoid.NavierStokes.ReferenceBarrier
