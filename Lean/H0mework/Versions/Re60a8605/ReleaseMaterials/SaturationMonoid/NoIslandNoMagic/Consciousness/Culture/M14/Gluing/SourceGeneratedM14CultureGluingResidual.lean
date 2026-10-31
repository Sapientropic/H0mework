import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication.SourceGeneratedM14ActualRelationCultureNetwork

/-!
# Source-generated M14 culture gluing residual

The transmission cochain is compiled from the three actual target-consumer
effects of the M14 communication network.  It is then proved equal to the
existing actual relation-cycle cochain.  Residual magnitude three,
nontrivial H¹, and failure of path additivity are therefore outputs of the
same generated communication events, not gluing premises.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Gluing

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution
open M14ProofCarryingActualRelationThreeCycleResidual
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication

noncomputable section

/-- Public culture cochain read only from actual delivery effects on selected
cycle edges. -/
def m14CultureTransmissionCochainAt
    (base : Nat) : ThreeCycleTime → ThreeCycleTime → Int :=
  fun source target =>
    if target = threeCycleNext source then
      (show Int from (m14CultureEdgeDeliveryAt base source).effect)
    else
      0

@[simp] theorem m14CultureTransmissionCochain_selectedEdge
    (base : Nat) (source : ThreeCycleTime) :
    m14CultureTransmissionCochainAt base source
      (threeCycleNext source) = 1 := by
  simp [m14CultureTransmissionCochainAt,
    m14CultureEdgeDelivery_effect_eq_one]

/-- Mechanism-faithfulness: the delivery-generated cochain is literally the
existing actual relation-cycle cochain. -/
theorem m14CultureTransmissionCochain_eq_actualRelationCycleCochain
    (base : Nat) :
    m14CultureTransmissionCochainAt base =
      actualRelationCycleCochain base := by
  funext source target
  by_cases selected : target = threeCycleNext source
  · subst target
    rw [m14CultureTransmissionCochain_selectedEdge,
      actualRelationCycleCochain_selectedEdge]
  · simp [m14CultureTransmissionCochainAt,
      actualRelationCycleCochain, selected]

theorem m14CultureTransmissionResidual_eq_three (base : Nat) :
    threeAgentRingResidual (m14CultureTransmissionCochainAt base) = 3 := by
  rw [m14CultureTransmissionCochain_eq_actualRelationCycleCochain]
  exact actualRelationCycle_residual_eq_three base

theorem m14CultureTransmissionResidualMagnitude_eq_three (base : Nat) :
    threeAgentRingResidualMagnitude
      (m14CultureTransmissionCochainAt base) = 3 := by
  rw [m14CultureTransmissionCochain_eq_actualRelationCycleCochain]
  exact actualRelationCycle_residualMagnitude_eq_three base

theorem m14CultureTransmission_nontrivial_h1 (base : Nat) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime Int)
      (m14CultureTransmissionCochainAt base) := by
  rw [m14CultureTransmissionCochain_eq_actualRelationCycleCochain]
  exact actualRelationCycle_nontrivial_h1 base

theorem m14CultureTransmission_not_pathAdditive (base : Nat) :
    Not (PathAdditive (m14CultureTransmissionCochainAt base)) := by
  rw [m14CultureTransmissionCochain_eq_actualRelationCycleCochain]
  exact actualRelationCycle_not_pathAdditive base

theorem m14CultureTransmission_not_edgeExact (base : Nat) :
    Not (ThreeAgentRingEdgeExact
      (m14CultureTransmissionCochainAt base)) := by
  rw [m14CultureTransmissionCochain_eq_actualRelationCycleCochain]
  exact actualRelationCycle_not_edgeExact base

/-- Same practice medium after one closed transport does not erase the
ordered three-event history or its H¹ residual. -/
theorem m14CultureSamePractice_nontrivialHistory (base : Nat) :
    (m14CultureCycleDeliveryAt base).targetValue =
        (m14CultureCycleDeliveryAt base).sourceValue ∧
      (m14CultureCyclePathAt base).events ≠ [] ∧
      threeAgentRingResidual
        (m14CultureTransmissionCochainAt base) = 3 ∧
      CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        (m14CultureTransmissionCochainAt base) := by
  refine ⟨m14CultureCycleDelivery_targetValue_eq_sourceValue base,
    ?_, m14CultureTransmissionResidual_eq_three base,
    m14CultureTransmission_nontrivial_h1 base⟩
  intro eventsEmpty
  have lengthEquality := congrArg List.length eventsEmpty
  change 3 = 0 at lengthEquality
  omega

structure SourceGeneratedM14CultureGluingResidualAt
    (base : Nat) : Type where
  private mk ::
  communication :
    type_of% (sourceGeneratedM14ActualRelationCultureNetwork_directConsumer
      base)
  cochainExact : m14CultureTransmissionCochainAt base =
    actualRelationCycleCochain base
  residualExact : threeAgentRingResidual
    (m14CultureTransmissionCochainAt base) = 3
  h1 : CechAdditiveCover.H1Obstruction
    (identityPairZeroTripleCover ThreeCycleTime Int)
    (m14CultureTransmissionCochainAt base)
  notPathAdditive : Not (PathAdditive
    (m14CultureTransmissionCochainAt base))
  samePracticeNontrivialHistory :
    type_of% (m14CultureSamePractice_nontrivialHistory base)

def sourceGeneratedM14CultureGluingResidualAt (base : Nat) :
    SourceGeneratedM14CultureGluingResidualAt base where
  communication :=
    sourceGeneratedM14ActualRelationCultureNetwork_directConsumer base
  cochainExact :=
    m14CultureTransmissionCochain_eq_actualRelationCycleCochain base
  residualExact := m14CultureTransmissionResidual_eq_three base
  h1 := m14CultureTransmission_nontrivial_h1 base
  notPathAdditive := m14CultureTransmission_not_pathAdditive base
  samePracticeNontrivialHistory :=
    m14CultureSamePractice_nontrivialHistory base

theorem sourceGeneratedM14CultureGluingResidual_directConsumer
    (base : Nat) :
    Nonempty (SourceGeneratedM14CultureGluingResidualAt base) ∧
      type_of% (sourceGeneratedM14ActualRelationCultureNetwork_directConsumer
        base) ∧
      m14CultureTransmissionCochainAt base =
        actualRelationCycleCochain base ∧
      threeAgentRingResidual
        (m14CultureTransmissionCochainAt base) = 3 ∧
      threeAgentRingResidualMagnitude
        (m14CultureTransmissionCochainAt base) = 3 ∧
      CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        (m14CultureTransmissionCochainAt base) ∧
      Not (PathAdditive (m14CultureTransmissionCochainAt base)) ∧
      Not (ThreeAgentRingEdgeExact
        (m14CultureTransmissionCochainAt base)) ∧
      type_of% (m14CultureSamePractice_nontrivialHistory base) :=
  ⟨⟨sourceGeneratedM14CultureGluingResidualAt base⟩,
    sourceGeneratedM14ActualRelationCultureNetwork_directConsumer base,
    m14CultureTransmissionCochain_eq_actualRelationCycleCochain base,
    m14CultureTransmissionResidual_eq_three base,
    m14CultureTransmissionResidualMagnitude_eq_three base,
    m14CultureTransmission_nontrivial_h1 base,
    m14CultureTransmission_not_pathAdditive base,
    m14CultureTransmission_not_edgeExact base,
    m14CultureSamePractice_nontrivialHistory base⟩

end
end Gluing
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Gluing.m14CultureTransmissionCochain_eq_actualRelationCycleCochain
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Gluing.m14CultureTransmission_nontrivial_h1
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Gluing.m14CultureSamePractice_nontrivialHistory
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Gluing.sourceGeneratedM14CultureGluingResidual_directConsumer
