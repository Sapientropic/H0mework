import H0mework.Physics.SourceFamily.OccurrenceTrace

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFamilyOccurrence

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField
open StageNineCClassicalWorldAcceptance StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeMotherAction
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous Stage9C.Reduction SourceFamily

noncomputable section

def sourceClock (source : SmoothUnifiedSource) : ℝ :=
  Real.sqrt (gaugeScale^3 / (2*source.legacy.sigma*spinScale))

def sourcePhaseRate (source : SmoothUnifiedSource) : ℝ :=
  3*sourceClock source/2*(spinScale-gaugeScale)

/-- The complete field is computed from the history-produced source, the
original materials and the same joint Cartan/constitutive writer. -/
def materialField (source : SmoothUnifiedSource) : StageNineHolonomicConfiguration :=
  algebraicCartanReduction source
    { Runtime.configuration with
      coframe := fun _ => homogeneousCoframe (sourceClock source)
      gaugeConnection := fun _ => gaugePotential gaugeScale
      scalar := fun _ => sourceGeneratedVacuumCoordinates source
      matter := fun point => spinPairMatter
        (phase (sourcePhaseRate source) point) (phase (-sourcePhaseRate source) point)
      conjugateMatter := fun point => spinPairDual
        ((spinScale : ℂ)*phase (sourcePhaseRate source) point)
        ((spinScale : ℂ)*phase (-sourcePhaseRate source) point) }

theorem materialField_family (step : ℕ) : materialField (sourceAt step) = fieldAt step := rfl

def formedField (visit : MotherVisit) : StageNineHolonomicConfiguration :=
  materialField (formedSource visit)

def formedAction (visit : MotherVisit) (chart : StageNineChart) (point : BasePoint) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (formedSource visit) chart point
    (toContinuumPointField (formedField visit) point)

theorem field_at (step : ℕ) : formedField (Stage9C.Revision.SpinPair.visit (10+step)) = fieldAt step := by
  rw [formedField, formed_at, materialField_family]

theorem field_next (visit : MotherVisit)
    (afterOrigin : originDepth ≤ Stage9C.Revision.temporalDepth visit.history) :
    formedField (visit.next rfl) = materialField (advanceSource (formedSource visit)) :=
  congrArg materialField (formed_next visit afterOrigin)

theorem action_next (visit : MotherVisit)
    (afterOrigin : originDepth ≤ Stage9C.Revision.temporalDepth visit.history)
    (chart : StageNineChart) (point : BasePoint) :
    formedAction (visit.next rfl) chart point =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (advanceSource (formedSource visit))
        chart point (toContinuumPointField (materialField (advanceSource (formedSource visit))) point) := by
  unfold formedAction formedField
  rw [formed_next visit afterOrigin]

theorem field_accepted (visit : MotherVisit) :
    ClassicalWorldAcceptance (formedSource visit) (formedField visit) := by
  unfold formedField
  rw [formed_normal, materialField_family]
  exact accepted _

theorem physical_clock (visit : MotherVisit) (point : BasePoint) :
    (formedField visit).coframe point = homogeneousCoframe (sourceClock (formedSource visit)) := rfl

theorem origin_field : formedField Runtime.visit = Runtime.configuration := by
  exact (field_at 0).trans field_zero

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFamilyOccurrence
