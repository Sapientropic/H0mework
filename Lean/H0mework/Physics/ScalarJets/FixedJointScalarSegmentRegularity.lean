import H0mework.Physics.Geometry.CanonicalTimePrimitiveSegmentRegularity
import H0mework.Physics.JointVariation.AdjointTemporalLocalRegularity
import H0mework.Physics.ElectricEC.FixedTemporalScalarAmbientFirstJetRegularity
import H0mework.Physics.FullOccurrence.FixedP286Verdict
import H0mework.Physics.ActualGerms.FixedJointTemporalMatterTimeAxisRegularity

/-!
# Fixed P506/L0 scalar regularity on the authoritative time segment

The fixed complete-joint scalar writer integrates the acceleration selected by
the mother action twice along the canonical source-to-occurrence segment.  On
the connected nondegenerate time-axis component, that whole segment stays in
the action's regularity corridor.  The finite-order parameter-integral
calculus therefore gives the literal U5 scalar a genuine ambient `C³` germ at
every authoritative contact.

No target first jet, residual coordinate, support branch, zero-fiber receipt,
or tunable coefficient is consumed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalTimePrimitiveSegmentRegularity
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointTemporalMatterTimeAxisRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarVariation
open SU7MotherLieAlgebra
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff Interval Matrix.Norms.Elementwise Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance scalarSegmentMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance scalarSegmentP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance scalarSegmentP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance scalarSegmentP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FirstAcceleration : BasePoint → ScalarCoordinateCarrier :=
  completeJointScalarAccelerationProfile Source Input

private abbrev FirstMatterCorrection : BasePoint → MatterCoordinateCarrier :=
  completeJointMatterTemporalCoordinateCorrection Source Input

private abbrev FirstAdjointCorrection : BasePoint → MatterCoordinateCarrier :=
  completeJointAdjointTemporalCoordinateCorrection Source Input

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source Input

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev RecenteredU5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration U5 contact

private abbrev U5OccurrenceAcceleration (contact : BasePoint) :
    BasePoint → ScalarCoordinateCarrier :=
  completeJointScalarAccelerationProfile Source (RecenteredU5 contact)

private abbrev U5OccurrenceSecondPrimitive (contact : BasePoint) :
    BasePoint → ScalarCoordinateCarrier :=
  canonicalTimeSecondPrimitive (U5OccurrenceAcceleration contact)

private abbrev U5OccurrenceTemporal (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source (RecenteredU5 contact)

/-- The open carrier on which the fixed mother-action acceleration is read
from a nondegenerate coframe. -/
def fixedP506L0CompleteJointScalarAccelerationCorridor : Set BasePoint :=
  {point | Matrix.det (Input.coframe point) ≠ 0}

theorem fixedP506L0CompleteJointScalarAccelerationCorridor_open :
    IsOpen fixedP506L0CompleteJointScalarAccelerationCorridor := by
  have determinantSmooth : ContDiff ℝ ∞ fun point =>
      Matrix.det (Input.coframe point) := by
    rw [show (fun point => Matrix.det (Input.coframe point)) =
        fun point => ∑ permutation : Equiv.Perm LorentzianIndex,
          ((Equiv.Perm.sign permutation : ℤ) : ℝ) *
            ∏ index : LorentzianIndex,
              Input.coframe point (permutation index) index by
      funext point
      exact Matrix.det_apply' _]
    apply ContDiff.sum
    intro permutation _
    apply contDiff_const.mul
    apply contDiff_prod
    intro index _
    exact fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
      (permutation index) index
  exact isOpen_ne_fun determinantSmooth.continuous continuous_const

/-- The already generated fixed acceleration is `C⁵` on its exact open
nondegenerate corridor. -/
theorem fixedP506L0CompleteJointScalarAcceleration_contDiffOn_five :
    ContDiffOn ℝ 5 FirstAcceleration
      fixedP506L0CompleteJointScalarAccelerationCorridor := by
  intro point pointMem
  have finiteOrder : (5 : ℕ∞ω) ≤ ∞ := by
    change ((5 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact
    (fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt point
      pointMem).of_le finiteOrder |>.contDiffWithinAt

/-- Every finite differentiability order is available on the same fixed
action corridor; the corridor itself does not depend on the requested order. -/
theorem fixedP506L0CompleteJointScalarAcceleration_contDiffOn
    (order : ℕ) :
    ContDiffOn ℝ order FirstAcceleration
      fixedP506L0CompleteJointScalarAccelerationCorridor := by
  intro point pointMem
  have finiteOrder : (order : ℕ∞ω) ≤ ∞ := by
    change ((order : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact
    (fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt point
      pointMem).of_le finiteOrder |>.contDiffWithinAt

private theorem scaled_time_mem_uIcc
    (time parameter : ℝ)
    (parameterMem : parameter ∈ Set.Icc (0 : ℝ) 1) :
    time * parameter ∈ Set.uIcc 0 time := by
  rcases le_total 0 time with timeNonnegative | timeNonpositive
  · rw [Set.uIcc_of_le timeNonnegative]
    constructor <;> nlinarith [parameterMem.1, parameterMem.2]
  · rw [Set.uIcc_of_ge timeNonpositive]
    constructor <;> nlinarith [parameterMem.1, parameterMem.2]

private theorem timeInterval_subset_timeAxisDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Set.uIcc 0 time ⊆ fixedP506L0FinalCommonTimeAxisOriginDomain space := by
  have ordConnected :
      Set.OrdConnected (fixedP506L0FinalCommonTimeAxisOriginDomain space) :=
    isPreconnected_iff_ordConnected.mp
      (fixedP506L0FinalCommonTimeAxisOriginDomain_connected space
        ).isPreconnected
  exact ordConnected.uIcc_subset
    (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space) inDomain

/-- Connectedness of the authoritative time-axis component keeps the whole
canonical integration segment inside the mother action's nondegenerate
corridor. -/
theorem fixedP506L0CompleteJointScalar_canonicalTimeSegment_subset_corridor
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    canonicalTimeSegment (canonicalCauchySlicePoint time space) ⊆
      fixedP506L0CompleteJointScalarAccelerationCorridor := by
  rintro point ⟨parameter, parameterMem, rfl⟩
  change
    canonicalNormalizedTimeSlice parameter
        (canonicalCauchySlicePoint time space) ∈
      fixedP506L0CompleteJointScalarAccelerationCorridor
  rw [canonicalNormalizedTimeSlice_apply,
    canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  have scaledInDomain :
      time * parameter ∈
        fixedP506L0FinalCommonTimeAxisOriginDomain space :=
    timeInterval_subset_timeAxisDomain time space inDomain
      (scaled_time_mem_uIcc time parameter parameterMem)
  change Matrix.det
      (Input.coframe (canonicalCauchySlicePoint (time * parameter) space)) ≠ 0
  rw [← fixedP506L0CompleteJointGlobalDevelopmentActual_coframe]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
      space scaledInDomain

/-- The first mother-action scalar second primitive has an ambient `C³` germ
at every point of the authoritative time-axis component. -/
theorem fixedP506L0CompleteJointScalarSecondPrimitive_contDiffAt_three
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ 3
      (canonicalTimeSecondPrimitive FirstAcceleration)
      (canonicalCauchySlicePoint time space) := by
  exact
    canonicalTimeSecondPrimitive_contDiffAt_three_of_contDiffOn_five_segment
      FirstAcceleration fixedP506L0CompleteJointScalarAccelerationCorridor
      fixedP506L0CompleteJointScalarAccelerationCorridor_open
      fixedP506L0CompleteJointScalarAcceleration_contDiffOn_five
      (canonicalCauchySlicePoint time space)
      (fixedP506L0CompleteJointScalar_canonicalTimeSegment_subset_corridor
        time space inDomain)

/-- The action-owned second primitive has every finite ambient derivative at
an authoritative contact.  Each order is generated from the same corridor,
with the finite two-derivative integration cost made explicit. -/
theorem fixedP506L0CompleteJointScalarSecondPrimitive_contDiffAt
    (order : ℕ)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ order
      (canonicalTimeSecondPrimitive FirstAcceleration)
      (canonicalCauchySlicePoint time space) := by
  exact
    canonicalTimeSecondPrimitive_contDiffAt_of_contDiffOn_segment_finite
      order FirstAcceleration
      fixedP506L0CompleteJointScalarAccelerationCorridor
      fixedP506L0CompleteJointScalarAccelerationCorridor_open
      (fixedP506L0CompleteJointScalarAcceleration_contDiffOn (order + 2))
      (canonicalCauchySlicePoint time space)
      (fixedP506L0CompleteJointScalar_canonicalTimeSegment_subset_corridor
        time space inDomain)

private theorem u5_scalar_eq_temporal : U5.scalar = Temporal.scalar := by
  calc
    U5.scalar =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.scalar :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC
    _ = fixedP506L0CompleteJointGlobalDevelopmentActual.scalar :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing
    _ = Temporal.scalar := by rfl

/-- The literal action-generated U5 scalar, not a contact proxy, is ambient
`C³` at every authoritative time-axis contact. -/
theorem fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_contDiffAt_three
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ 3 U5.scalar
      (canonicalCauchySlicePoint time space) := by
  have finiteOrder : (3 : ℕ∞ω) ≤ ∞ := by
    change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  rw [u5_scalar_eq_temporal]
  change ContDiffAt ℝ 3
    (fun point =>
      Input.scalar point +
        canonicalTimeSecondPrimitive FirstAcceleration point)
    (canonicalCauchySlicePoint time space)
  exact
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
      ).contDiffAt.of_le finiteOrder |>.add
      (fixedP506L0CompleteJointScalarSecondPrimitive_contDiffAt_three
        time space inDomain)

/-- The literal U5 scalar is smoothly generated at every point of the
authoritative time-axis component.  This is a pointwise `C∞` statement in the
full ambient spacetime carrier, obtained from all finite segment orders. -/
theorem fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_contDiffAt
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ ∞ U5.scalar
      (canonicalCauchySlicePoint time space) := by
  rw [contDiffAt_infty]
  intro order
  rw [u5_scalar_eq_temporal]
  change ContDiffAt ℝ order
    (fun point =>
      Input.scalar point +
        canonicalTimeSecondPrimitive FirstAcceleration point)
    (canonicalCauchySlicePoint time space)
  have finiteOrder : (order : ℕ∞ω) ≤ ∞ := by
    change ((order : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
      ).contDiffAt.of_le finiteOrder |>.add
      (fixedP506L0CompleteJointScalarSecondPrimitive_contDiffAt order
        time space inDomain)

/-! ## Primal matter segment regularity -/

/-- The finite-order regularity locus of the already generated primal matter
correction.  Its openness follows from local finite differentiability, so no
extra radius or neighborhood is selected by the source. -/
def fixedP506L0CompleteJointMatterCorrectionRegularityCorridor
    (order : ℕ) : Set BasePoint :=
  {point | ContDiffAt ℝ order FirstMatterCorrection point}

theorem fixedP506L0CompleteJointMatterCorrectionRegularityCorridor_open
    (order : ℕ) :
    IsOpen (fixedP506L0CompleteJointMatterCorrectionRegularityCorridor
      order) := by
  rw [isOpen_iff_mem_nhds]
  intro point pointMem
  change ContDiffAt ℝ order FirstMatterCorrection point at pointMem
  exact pointMem.eventually (by simp)

theorem fixedP506L0CompleteJointMatterCorrection_contDiffOn
    (order : ℕ) :
    ContDiffOn ℝ order FirstMatterCorrection
      (fixedP506L0CompleteJointMatterCorrectionRegularityCorridor order) := by
  intro point pointMem
  change ContDiffAt ℝ order FirstMatterCorrection point at pointMem
  exact pointMem.contDiffWithinAt

theorem fixedP506L0CompleteJointMatter_canonicalTimeSegment_subset_corridor
    (order : ℕ)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    canonicalTimeSegment (canonicalCauchySlicePoint time space) ⊆
      fixedP506L0CompleteJointMatterCorrectionRegularityCorridor order := by
  rintro point ⟨parameter, parameterMem, rfl⟩
  change ContDiffAt ℝ order FirstMatterCorrection
    (canonicalNormalizedTimeSlice parameter
      (canonicalCauchySlicePoint time space))
  rw [canonicalNormalizedTimeSlice_apply,
    canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  have scaledInDomain :
      time * parameter ∈
        fixedP506L0FinalCommonTimeAxisOriginDomain space :=
    timeInterval_subset_timeAxisDomain time space inDomain
      (scaled_time_mem_uIcc time parameter parameterMem)
  have regularInfinite :=
    fixedP506L0CompleteJointTemporalMatterCorrection_contDiffAt_on_timeAxisDomain
      (time * parameter) space scaledInDomain
  have finiteOrder : (order : ℕ∞ω) ≤ ∞ := by
    change ((order : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact regularInfinite.of_le finiteOrder

/-- The canonical primal matter primitive has every finite ambient
derivative at an authoritative contact. -/
theorem fixedP506L0CompleteJointMatterTemporalPrimitive_contDiffAt
    (order : ℕ)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ order
      (canonicalTimePrimitive FirstMatterCorrection)
      (canonicalCauchySlicePoint time space) := by
  exact
    canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment_finite
      order FirstMatterCorrection
      (fixedP506L0CompleteJointMatterCorrectionRegularityCorridor (order + 1))
      (fixedP506L0CompleteJointMatterCorrectionRegularityCorridor_open
        (order + 1))
      (fixedP506L0CompleteJointMatterCorrection_contDiffOn (order + 1))
      (canonicalCauchySlicePoint time space)
      (fixedP506L0CompleteJointMatter_canonicalTimeSegment_subset_corridor
        (order + 1) time space inDomain)

private theorem u5_matter_eq_temporal : U5.matter = Temporal.matter := by
  calc
    U5.matter =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.matter :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC
    _ = fixedP506L0CompleteJointGlobalDevelopmentActual.matter :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_eq_existing
    _ = Temporal.matter := by rfl

/-- Faithful finite coordinates of the literal U5 primal matter field are
smooth at every authoritative contact. -/
theorem fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matterCoordinates_contDiffAt
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ ∞
      (fun point => matterCoordinateEquiv (U5.matter point))
      (canonicalCauchySlicePoint time space) := by
  rw [contDiffAt_infty]
  intro order
  rw [u5_matter_eq_temporal]
  rw [show
    (fun point => matterCoordinateEquiv (Temporal.matter point)) =
      fun point =>
        matterCoordinateEquiv (Input.matter point) +
          canonicalTimePrimitive FirstMatterCorrection point by
    funext point
    unfold Temporal completeJointGlobalTemporalCurrent
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
    simp]
  have finiteOrder : (order : ℕ∞ω) ≤ ∞ := by
    change ((order : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
      ).contDiffAt.of_le finiteOrder |>.add
      (fixedP506L0CompleteJointMatterTemporalPrimitive_contDiffAt order
        time space inDomain)

/-! ## Independent adjoint segment regularity -/

def fixedP506L0CompleteJointAdjointCorrectionRegularityCorridor
    (order : ℕ) : Set BasePoint :=
  {point | ContDiffAt ℝ order FirstAdjointCorrection point}

theorem fixedP506L0CompleteJointAdjointCorrectionRegularityCorridor_open
    (order : ℕ) :
    IsOpen (fixedP506L0CompleteJointAdjointCorrectionRegularityCorridor
      order) := by
  rw [isOpen_iff_mem_nhds]
  intro point pointMem
  change ContDiffAt ℝ order FirstAdjointCorrection point at pointMem
  exact pointMem.eventually (by simp)

theorem fixedP506L0CompleteJointAdjointCorrection_contDiffOn
    (order : ℕ) :
    ContDiffOn ℝ order FirstAdjointCorrection
      (fixedP506L0CompleteJointAdjointCorrectionRegularityCorridor order) := by
  intro point pointMem
  change ContDiffAt ℝ order FirstAdjointCorrection point at pointMem
  exact pointMem.contDiffWithinAt

theorem fixedP506L0CompleteJointAdjoint_canonicalTimeSegment_subset_corridor
    (order : ℕ)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    canonicalTimeSegment (canonicalCauchySlicePoint time space) ⊆
      fixedP506L0CompleteJointAdjointCorrectionRegularityCorridor order := by
  rintro point ⟨parameter, parameterMem, rfl⟩
  change ContDiffAt ℝ order FirstAdjointCorrection
    (canonicalNormalizedTimeSlice parameter
      (canonicalCauchySlicePoint time space))
  rw [canonicalNormalizedTimeSlice_apply,
    canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
  have scaledInDomain :
      time * parameter ∈
        fixedP506L0FinalCommonTimeAxisOriginDomain space :=
    timeInterval_subset_timeAxisDomain time space inDomain
      (scaled_time_mem_uIcc time parameter parameterMem)
  have coframeNondegenerate :
      Matrix.det
          (Input.coframe
            (canonicalCauchySlicePoint (time * parameter) space)) ≠ 0 := by
    rw [← fixedP506L0CompleteJointGlobalDevelopmentActual_coframe]
    exact
      fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
        space scaledInDomain
  have temporalPrincipalNonzero :
      coframeTemporalPrincipalScalar
          (Input.coframe
            (canonicalCauchySlicePoint (time * parameter) space)) ≠ 0 := by
    rw [fixedP506L0CompleteJointTemporalInput_coframe_eq_finalCommon,
      fixedP506L0FinalCommonTimeAxis_temporalPrincipalScalar_eq_one
        space (time * parameter) scaledInDomain]
    exact one_ne_zero
  have regularInfinite :=
    completeJointAdjointTemporalCoordinateCorrection_contDiffAt_infty
      Source Input fixedP506FormNativeJointActionSolvedSuccessor_smooth
      (canonicalCauchySlicePoint (time * parameter) space)
      coframeNondegenerate temporalPrincipalNonzero
  have finiteOrder : (order : ℕ∞ω) ≤ ∞ := by
    change ((order : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact regularInfinite.of_le finiteOrder

/-- The independent-dual action profile generates a smooth canonical first
primitive on every authoritative source-to-contact segment. -/
theorem fixedP506L0CompleteJointAdjointTemporalPrimitive_contDiffAt
    (order : ℕ)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ order
      (canonicalTimePrimitive FirstAdjointCorrection)
      (canonicalCauchySlicePoint time space) := by
  exact
    canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment_finite
      order FirstAdjointCorrection
      (fixedP506L0CompleteJointAdjointCorrectionRegularityCorridor
        (order + 1))
      (fixedP506L0CompleteJointAdjointCorrectionRegularityCorridor_open
        (order + 1))
      (fixedP506L0CompleteJointAdjointCorrection_contDiffOn (order + 1))
      (canonicalCauchySlicePoint time space)
      (fixedP506L0CompleteJointAdjoint_canonicalTimeSegment_subset_corridor
        (order + 1) time space inDomain)

private theorem u5_conjugateMatter_eq_temporal :
    U5.conjugateMatter = Temporal.conjugateMatter := by
  calc
    U5.conjugateMatter =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.conjugateMatter :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC
    _ = fixedP506L0CompleteJointGlobalDevelopmentActual.conjugateMatter :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_eq_existing
    _ = Temporal.conjugateMatter := by rfl

/-- Faithful coordinates of the literal U5 independent-dual field are smooth
at every authoritative contact. -/
theorem fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatterCoordinates_contDiffAt
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ ∞ (holonomicConjugateMatterCoordinates U5)
      (canonicalCauchySlicePoint time space) := by
  rw [contDiffAt_infty]
  intro order
  rw [show holonomicConjugateMatterCoordinates U5 =
      fun point =>
        holonomicConjugateMatterCoordinates Input point +
          canonicalTimePrimitive FirstAdjointCorrection point by
    unfold holonomicConjugateMatterCoordinates
    rw [u5_conjugateMatter_eq_temporal,
      completeJointGlobalTemporalCurrent_conjugateMatter]
    funext point
    simp only [matterDualCoordinates_add,
      matterDualCoordinates_matterDualOfCoordinates]
  ]
  have finiteOrder : (order : ℕ∞ω) ≤ ∞ := by
    change ((order : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact
    (holonomicConjugateMatterCoordinates_contDiff Input
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
      ).contDiffAt.of_le finiteOrder |>.add
      (fixedP506L0CompleteJointAdjointTemporalPrimitive_contDiffAt order
        time space inDomain)

/-! ## U5 scalar Euler regularity from the same local action data -/

private theorem u5_coframe_eq_input : U5.coframe = Input.coframe := by
  calc
    U5.coframe =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.coframe :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC
    _ = fixedP506L0CompleteJointGlobalDevelopmentActual.coframe :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing
    _ = Input.coframe :=
      fixedP506L0CompleteJointGlobalDevelopmentActual_coframe

private theorem u5_coframe_contDiff : ContDiff ℝ ∞ U5.coframe := by
  rw [u5_coframe_eq_input]
  exact holonomicCoframe_contDiff Input
    fixedP506FormNativeJointActionSolvedSuccessor_smooth

theorem scalarCovariantDerivative_contDiffAt_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (scalarRegular : ContDiffAt ℝ ∞ current.scalar point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        holonomicScalarCovariantDerivative current candidate direction)
      point := by
  unfold holonomicScalarCovariantDerivative
  apply ContDiffAt.add
  · unfold fieldDirectionalDerivative
    exact (scalarRegular.fderiv_right (by simp)).clm_apply contDiffAt_const
  · rw [show
      (fun candidate =>
        scalarMotherLieAction
          (p286LieBlockEmbed (current.gaugeConnection candidate direction))
          (current.scalar candidate)) =
        fun candidate =>
          StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
            (p286CoordinateEquiv
              (current.gaugeConnection candidate direction))
            (current.scalar candidate) by
      funext candidate
      change
        scalarMotherLieAction
            (p286LieBlockEmbed
              (current.gaugeConnection candidate direction))
            (current.scalar candidate) =
          scalarMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (p286CoordinateEquiv
                  (current.gaugeConnection candidate direction))))
            (current.scalar candidate)
      rw [p286CoordinateEquiv.symm_apply_apply]
    ]
    exact
      (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear.toContinuousBilinearMap.contDiff.contDiffAt.comp
        point (gaugeConnectionRegular direction)).clm_apply scalarRegular

private theorem scalarCoordinatePairingRe_contDiffAt
    {first second : BasePoint → ScalarCoordinateCarrier}
    {point : BasePoint}
    (firstRegular : ContDiffAt ℝ ∞ first point)
    (secondRegular : ContDiffAt ℝ ∞ second point) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        scalarCoordinatePairingRe (first candidate) (second candidate))
      point := by
  unfold scalarCoordinatePairingRe
  apply ContDiffAt.sum
  intro index _
  let coordinateLinear : ScalarCoordinateCarrier →L[ℝ] ℂ :=
    (PiLp.projₗ (𝕜 := ℂ) 2
      (fun _ : ScalarBasisIndex => ℂ) index).toContinuousLinearMap
        |>.restrictScalars ℝ
  have firstEntry : ContDiffAt ℝ ∞ (fun candidate => first candidate index)
      point := by
    change ContDiffAt ℝ ∞ (coordinateLinear ∘ first) point
    exact coordinateLinear.contDiff.contDiffAt.comp point firstRegular
  have secondEntry : ContDiffAt ℝ ∞
      (fun candidate => second candidate index) point := by
    change ContDiffAt ℝ ∞ (coordinateLinear ∘ second) point
    exact coordinateLinear.contDiff.contDiffAt.comp point secondRegular
  have conjugateFirst : ContDiffAt ℝ ∞
      (fun candidate => star (first candidate index)) point := by
    change ContDiffAt ℝ ∞
      (fun candidate => Complex.conjCLE (first candidate index)) point
    exact Complex.conjCLE.contDiff.contDiffAt.comp point firstEntry
  exact Complex.reCLM.contDiff.contDiffAt.comp point
    (conjugateFirst.mul secondEntry)

theorem scalarMomentum_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ current.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ current.scalar point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentum source current direction derivativeDirection)
      point := by
  have volumeRegular : ContDiffAt ℝ ∞
      (fun candidate => |Matrix.det (current.coframe candidate)|) point :=
    (coframe_volume_contDiffAt
      (current.coframe point) coframeNondegenerate).comp
        point coframeRegular
  have metricRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (lorentzianMetricOfCoframe (current.coframe candidate))⁻¹) point :=
    (lorentzianMetric_inv_contDiffAt
      (current.coframe point) coframeNondegenerate).comp
        point coframeRegular
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative generatedVolumeDensity
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  apply volumeRegular.mul
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro first _
  apply ContDiffAt.sum
  intro second _
  apply (contDiffAt_pi.mp (contDiffAt_pi.mp metricRegular first) second).mul
  exact
    (scalarCoordinatePairingRe_contDiffAt contDiffAt_const
      (scalarCovariantDerivative_contDiffAt_of_local current point
        scalarRegular gaugeConnectionRegular second)
      ).add
      (scalarCoordinatePairingRe_contDiffAt
        (scalarCovariantDerivative_contDiffAt_of_local current point
          scalarRegular gaugeConnectionRegular first)
        contDiffAt_const)

private theorem scalarDivergence_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ current.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ current.scalar point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (scalarDifferentialMomentumDivergence source current direction) point := by
  unfold scalarDifferentialMomentumDivergence
  apply ContDiffAt.sum
  intro derivativeDirection _
  unfold fieldDirectionalDerivative
  exact
    ((scalarMomentum_contDiffAt_of_local source current point
      coframeNondegenerate coframeRegular scalarRegular
      gaugeConnectionRegular direction derivativeDirection).fderiv_right
        (by simp)).clm_apply contDiffAt_const

private theorem scalarVariation_contDiffAt_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    (direction : ScalarCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        scalarMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection candidate formDirection))
          direction)
      point := by
  rw [show
    (fun candidate =>
      scalarMotherLieAction
        (p286LieBlockEmbed
          (current.gaugeConnection candidate formDirection))
        direction) =
      fun candidate =>
        StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
          (p286CoordinateEquiv
            (current.gaugeConnection candidate formDirection)) direction by
    funext candidate
    change
      scalarMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection candidate formDirection))
          direction =
        scalarMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (current.gaugeConnection candidate formDirection)))) direction
    rw [p286CoordinateEquiv.symm_apply_apply]
  ]
  exact
    (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear.toContinuousBilinearMap.contDiff.contDiffAt.comp
      point (gaugeConnectionRegular formDirection)).clm_apply contDiffAt_const

private theorem scalarYukawaVectorCoordinates_contDiffAt_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (matterRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (current.matter candidate)) point)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        matterCoordinateEquiv
          (diracDualScalarYukawaVariationVector
            (toContinuumPointField current candidate) direction))
      point := by
  have actual :=
    (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
      |>.contDiffAt.comp point
        (contDiffAt_const : ContDiffAt ℝ ∞
          (fun _ : BasePoint => direction) point)).clm_apply matterRegular
  change ContDiffAt ℝ ∞
    (fun candidate =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (current.matter candidate))))) point at actual
  simpa only [diracDualScalarYukawaVariationVector, toContinuumPointField,
    matterCoordinateEquiv.symm_apply_apply] using actual

private theorem scalarYukawa_contDiffAt_of_local
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (matterRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (current.matter candidate)) point)
    (conjugateRegular : ContDiffAt ℝ ∞
      (holonomicConjugateMatterCoordinates current) point)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (fun candidate =>
        diracDualScalarYukawaFirstVariationDensity
          (toContinuumPointField current candidate) direction)
      point := by
  have vectorRegular :=
    scalarYukawaVectorCoordinates_contDiffAt_of_local current point
      matterRegular direction
  let pairingSum : BasePoint → ℂ := fun candidate =>
    ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
          (diracDualScalarYukawaVariationVector
          (toContinuumPointField current candidate) direction) index *
        holonomicConjugateMatterCoordinates current candidate index
  have pairingEquality :
      (fun candidate =>
        current.conjugateMatter candidate
          (diracDualScalarYukawaVariationVector
            (toContinuumPointField current candidate) direction)) =
        pairingSum := by
    funext candidate
    rw [← matterDualOfCoordinates_surjective
      (current.conjugateMatter candidate)]
    exact matterDualOfCoordinates_apply _ _
  have pairingRegular : ContDiffAt ℝ ∞ pairingSum point := by
    unfold pairingSum
    apply ContDiffAt.sum
    intro index _
    let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
      (PiLp.projₗ (𝕜 := ℂ) 2
        (fun _ : MatterCoordinateIndex => ℂ) index).toContinuousLinearMap
          |>.restrictScalars ℝ
    exact
      (projection.contDiff.contDiffAt.comp point vectorRegular).mul
        (projection.contDiff.contDiffAt.comp point conjugateRegular)
  unfold diracDualScalarYukawaFirstVariationDensity
  change ContDiffAt ℝ ∞
      (Complex.reCLM ∘ fun candidate =>
      current.conjugateMatter candidate
        (diracDualScalarYukawaVariationVector
          (toContinuumPointField current candidate) direction)) point
  rw [pairingEquality]
  exact Complex.reCLM.contDiff.contDiffAt.comp point pairingRegular

private theorem scalarAlgebraic_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ current.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ current.scalar point)
    (matterRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (current.matter candidate)) point)
    (conjugateRegular : ContDiffAt ℝ ∞
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (diracDualScalarAlgebraicDirectionalCoefficient source current direction)
      point := by
  have volumeRegular : ContDiffAt ℝ ∞
      (fun candidate => |Matrix.det (current.coframe candidate)|) point :=
    (coframe_volume_contDiffAt
      (current.coframe point) coframeNondegenerate).comp
        point coframeRegular
  have metricRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (lorentzianMetricOfCoframe (current.coframe candidate))⁻¹) point :=
    (lorentzianMetric_inv_contDiffAt
      (current.coframe point) coframeNondegenerate).comp
        point coframeRegular
  have kineticRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        scalarGaugeConnectionKineticFirstVariationDensity source 0 candidate
          (toContinuumPointField current candidate)
          (holonomicScalarVariationAlgebraicDirection current direction
            candidate)) point := by
    unfold scalarGaugeConnectionKineticFirstVariationDensity
      scalarFrameRelativeCovariantDerivative
      holonomicScalarVariationAlgebraicDirection
    simp only [toContinuumPointField,
      scalarFrameRelativeCoordinates_zeroChart]
    apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro first _
    apply ContDiffAt.sum
    intro second _
    apply (contDiffAt_pi.mp (contDiffAt_pi.mp metricRegular first) second).mul
    exact
      (scalarCoordinatePairingRe_contDiffAt
        (scalarVariation_contDiffAt_of_local current point
          gaugeConnectionRegular direction first)
        (scalarCovariantDerivative_contDiffAt_of_local current point
          scalarRegular gaugeConnectionRegular second)
        ).add
        (scalarCoordinatePairingRe_contDiffAt
          (scalarCovariantDerivative_contDiffAt_of_local current point
            scalarRegular gaugeConnectionRegular first)
          (scalarVariation_contDiffAt_of_local current point
            gaugeConnectionRegular direction second))
  have potentialRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        scalarPotentialFirstVariation source
          (toContinuumPointField current candidate) direction) point := by
    unfold scalarPotentialFirstVariation frameRelativeScalarGradient
    exact contDiffAt_const.mul
      (scalarCoordinatePairingRe_contDiffAt
        (scalarRegular.sub contDiffAt_const) contDiffAt_const)
  unfold diracDualScalarAlgebraicDirectionalCoefficient generatedVolumeDensity
  exact volumeRegular.mul
    ((kineticRegular.sub potentialRegular).add
      (scalarYukawa_contDiffAt_of_local current point matterRegular
        conjugateRegular direction))

private theorem scalarEuler_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ current.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ current.scalar point)
    (matterRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (current.matter candidate)) point)
    (conjugateRegular : ContDiffAt ℝ ∞
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point)
    (direction : ScalarCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (diracDualScalarEulerLagrangeDirectionalCoefficient source current
        direction) point := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  exact
    (scalarAlgebraic_contDiffAt_of_local source current point
      coframeNondegenerate coframeRegular scalarRegular matterRegular
      conjugateRegular gaugeConnectionRegular direction).sub
      (scalarDivergence_contDiffAt_of_local source current point
        coframeNondegenerate coframeRegular scalarRegular
        gaugeConnectionRegular direction)

private theorem genericGeneratedAcceleration_eq_neg_coordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    genericDiracDualScalarGeneratedAcceleration source current =
      -genericDiracDualScalarTemporalDemandCoordinate source current := by
  unfold genericDiracDualScalarGeneratedAcceleration scalarActionRealDual
  congr 1
  apply PiLp.ext
  intro index
  change
    ((genericDiracDualScalarTemporalDemandDual source current
          (scalarRealBasis index) : ℂ) +
      (genericDiracDualScalarTemporalDemandDual source current
          (scalarImaginaryBasis index) : ℂ) * Complex.I) =
    ((genericDiracDualScalarRawTemporalDemand source current
          (scalarRealBasis index) : ℂ) +
      (genericDiracDualScalarRawTemporalDemand source current
          (scalarImaginaryBasis index) : ℂ) * Complex.I)
  rw [genericDiracDualScalarTemporalDemandDual_realBasis,
    genericDiracDualScalarTemporalDemandDual_imaginaryBasis]

/-- Local regularity of the complete-joint scalar acceleration generated from
one supplied current.  The mouth records only the current's primitive-field
regularity at the occurrence and coframe nondegeneracy there.  No residual,
target acceleration, zero-fiber receipt, or branch witness enters the
producer. -/
theorem completeJointScalarAccelerationProfile_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeNondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ ∞ current.coframe point)
    (scalarRegular : ContDiffAt ℝ ∞ current.scalar point)
    (matterRegular : ContDiffAt ℝ ∞
      (fun candidate => matterCoordinateEquiv (current.matter candidate)) point)
    (conjugateRegular : ContDiffAt ℝ ∞
      (holonomicConjugateMatterCoordinates current) point)
    (gaugeConnectionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate =>
          p286CoordinateEquiv
            (current.gaugeConnection candidate direction)) point) :
    ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile source current) point := by
  rw [show completeJointScalarAccelerationProfile source current =
      fun candidate =>
        -(EuclideanSpace.equiv ScalarBasisIndex ℂ).symm
          (fun index =>
            (diracDualScalarEulerLagrangeDirectionalCoefficient source current
                (scalarRealBasis index) candidate : ℂ) +
              (diracDualScalarEulerLagrangeDirectionalCoefficient source
                  current (scalarImaginaryBasis index) candidate : ℂ) *
                Complex.I) by
    funext candidate
    unfold completeJointScalarAccelerationProfile
    change
      genericDiracDualScalarGeneratedAcceleration source
          (completeJointRepairedConstitutiveCurrent source
            (completeJointGeneratedProfileRestartCurrent source current
              candidate)) = _
    rw [genericGeneratedAcceleration_eq_neg_coordinate]
    unfold genericDiracDualScalarTemporalDemandCoordinate
    apply congrArg Neg.neg
    apply congrArg (EuclideanSpace.equiv ScalarBasisIndex ℂ).symm
    funext index
    rw [completeJointScalarRawTemporalDemand_eq_currentScalarEuler,
      completeJointScalarRawTemporalDemand_eq_currentScalarEuler]
  ]
  apply ContDiffAt.neg
  let reconstruct :
      (ScalarBasisIndex → ℂ) →L[ℝ] ScalarCoordinateCarrier :=
    (EuclideanSpace.equiv ScalarBasisIndex ℂ).symm.toContinuousLinearMap
      |>.restrictScalars ℝ
  apply reconstruct.contDiff.contDiffAt.comp point
  apply contDiffAt_pi'
  intro index
  have realRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (diracDualScalarEulerLagrangeDirectionalCoefficient source current
          (scalarRealBasis index) candidate : ℂ)) point := by
    change ContDiffAt ℝ ∞
      (Complex.ofReal ∘
        diracDualScalarEulerLagrangeDirectionalCoefficient source current
          (scalarRealBasis index)) point
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp point
      (scalarEuler_contDiffAt_of_local source current point
        coframeNondegenerate coframeRegular scalarRegular matterRegular
        conjugateRegular gaugeConnectionRegular (scalarRealBasis index))
  have imaginaryRegular : ContDiffAt ℝ ∞
      (fun candidate =>
        (diracDualScalarEulerLagrangeDirectionalCoefficient source current
          (scalarImaginaryBasis index) candidate : ℂ)) point := by
    change ContDiffAt ℝ ∞
      (Complex.ofReal ∘
        diracDualScalarEulerLagrangeDirectionalCoefficient source current
          (scalarImaginaryBasis index)) point
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp point
      (scalarEuler_contDiffAt_of_local source current point
        coframeNondegenerate coframeRegular scalarRegular matterRegular
        conjugateRegular gaugeConnectionRegular (scalarImaginaryBasis index))
  exact realRegular.add (imaginaryRegular.mul contDiffAt_const)

/-- The second-sweep U5 scalar acceleration is locally smooth because it is
the faithful coordinate assembly of the same U5 scalar Euler read.  This is
the mother-action producer regularity theorem used by the arbitrary-contact
temporal write. -/
theorem fixedP506L0_U5_scalarAccelerationProfile_contDiffAt
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile Source U5)
      (canonicalCauchySlicePoint time space) := by
  let point := canonicalCauchySlicePoint time space
  have coframeNondegenerate : Matrix.det (U5.coframe point) ≠ 0 := by
    rw [u5_coframe_eq_input,
      ← fixedP506L0CompleteJointGlobalDevelopmentActual_coframe]
    exact
      fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
        space inDomain
  exact completeJointScalarAccelerationProfile_contDiffAt_of_local
    Source U5 point coframeNondegenerate u5_coframe_contDiff.contDiffAt
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_contDiffAt
      time space inDomain)
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matterCoordinates_contDiffAt
      time space inDomain)
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatterCoordinates_contDiffAt
      time space inDomain)
    (fun direction =>
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnectionCoordinate_contDiff
        direction).contDiffAt)

/-! ## Arbitrary-contact scalar first-jet authority -/

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem u5OccurrenceTemporal_scalar_eq_add_secondPrimitive
    (contact : BasePoint) :
    (U5OccurrenceTemporal contact).scalar =
      (RecenteredU5 contact).scalar +
        U5OccurrenceSecondPrimitive contact := by
  rfl

private theorem u5OccurrenceTemporal_gaugeConnection_eq
    (contact : BasePoint) :
    (U5OccurrenceTemporal contact).gaugeConnection =
      (RecenteredU5 contact).gaugeConnection := by
  rfl

private theorem u5OccurrenceTemporal_scalar_origin_eq
    (contact : BasePoint) :
    (U5OccurrenceTemporal contact).scalar 0 =
      (RecenteredU5 contact).scalar 0 := by
  rw [u5OccurrenceTemporal_scalar_eq_add_secondPrimitive]
  change
    (RecenteredU5 contact).scalar 0 +
        U5OccurrenceSecondPrimitive contact 0 =
      (RecenteredU5 contact).scalar 0
  rw [← canonicalCauchySlicePoint_zero_zero_local]
  simp only [U5OccurrenceSecondPrimitive,
    canonicalTimeSecondPrimitive_zeroSlice, add_zero]

private theorem canonicalSpacetimeContactTranslation_contDiff_local
    (contact : BasePoint) :
    ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation contact) := by
  unfold canonicalSpacetimeContactTranslation
  fun_prop

/-- Recenter naturality of the source/action-owned scalar acceleration.  The
selected contact is composed with the already generated profile; no target
jet, residual, support, or zero receipt is consumed. -/
theorem fixedP506L0_U5_occurrenceAcceleration_eq_translate
    (contact : BasePoint) :
    U5OccurrenceAcceleration contact =
      completeJointScalarAccelerationProfile Source U5 ∘
        canonicalSpacetimeContactTranslation contact := by
  funext point
  unfold U5OccurrenceAcceleration completeJointScalarAccelerationProfile
  change
    genericDiracDualScalarGeneratedAcceleration Source
        (completeJointRepairedConstitutiveCurrent Source
          (completeJointGeneratedProfileRestartCurrent Source
            (RecenteredU5 contact) point)) =
      genericDiracDualScalarGeneratedAcceleration Source
        (completeJointRepairedConstitutiveCurrent Source
          (completeJointGeneratedProfileRestartCurrent Source U5
            (canonicalSpacetimeContactTranslation contact point)))
  unfold completeJointGeneratedProfileRestartCurrent RecenteredU5
  rw [fullyRecenterHolonomicConfiguration_recenter]

private theorem fixedP506L0_U5_occurrenceAcceleration_contDiffAt
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ 1
      (U5OccurrenceAcceleration
        (canonicalCauchySlicePoint time space)) 0 := by
  rw [fixedP506L0_U5_occurrenceAcceleration_eq_translate]
  have profileRegular : ContDiffAt ℝ 1
      (completeJointScalarAccelerationProfile Source U5)
      (canonicalCauchySlicePoint time space) :=
    (fixedP506L0_U5_scalarAccelerationProfile_contDiffAt
      time space inDomain).of_le (by norm_num)
  have profileAtTranslation : ContDiffAt ℝ 1
      (completeJointScalarAccelerationProfile Source U5)
      (canonicalSpacetimeContactTranslation
        (canonicalCauchySlicePoint time space) 0) := by
    simpa [canonicalSpacetimeContactTranslation] using profileRegular
  exact profileAtTranslation.comp 0
    ((canonicalSpacetimeContactTranslation_contDiff_local
      (canonicalCauchySlicePoint time space)).contDiffAt.of_le
        (by norm_num))

private theorem u5OccurrenceTemporal_scalarFirstJet_eq_recentered
    (contact : BasePoint)
    (secondPrimitiveZeroJet :
      HasFDerivAt (U5OccurrenceSecondPrimitive contact)
        (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0) :
    holonomicScalarCovariantDerivative (U5OccurrenceTemporal contact) 0 =
      holonomicScalarCovariantDerivative (RecenteredU5 contact) 0 := by
  have derivativeEq (direction : LorentzianIndex) :
      fieldDirectionalDerivative (U5OccurrenceTemporal contact).scalar
          0 direction =
        fieldDirectionalDerivative (RecenteredU5 contact).scalar
          0 direction := by
    unfold fieldDirectionalDerivative
    rw [u5OccurrenceTemporal_scalar_eq_add_secondPrimitive]
    have secondPrimitiveDifferentiable :=
      secondPrimitiveZeroJet.differentiableAt
    by_cases currentDifferentiable :
        DifferentiableAt ℝ (RecenteredU5 contact).scalar 0
    · rw [fderiv_add currentDifferentiable secondPrimitiveDifferentiable,
        add_apply]
      have primitiveDerivativeZero :
          fderiv ℝ (U5OccurrenceSecondPrimitive contact) 0 = 0 :=
        secondPrimitiveZeroJet.fderiv
      rw [primitiveDerivativeZero, zero_apply, add_zero]
    · have generatedNotDifferentiable :
          ¬ DifferentiableAt ℝ
            ((RecenteredU5 contact).scalar +
              U5OccurrenceSecondPrimitive contact) 0 := by
        intro generatedDifferentiable
        apply currentDifferentiable
        have recovered :=
          generatedDifferentiable.sub secondPrimitiveDifferentiable
        simpa only [add_sub_cancel_right] using recovered
      rw [fderiv_zero_of_not_differentiableAt generatedNotDifferentiable,
        fderiv_zero_of_not_differentiableAt currentDifferentiable]
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [derivativeEq direction,
    congrFun (u5OccurrenceTemporal_gaugeConnection_eq contact) 0,
    u5OccurrenceTemporal_scalar_origin_eq contact]

/-- At every authoritative fixed P506/L0 contact, the scalar mother-action
temporal write preserves the complete covariant first jet of the same
recentered U5 current.  The result is generated by the action Euler profile's
local regularity and the canonical second primitive's zero first jet; it does
not assert the unrelated U6h horizontal relation `D₀φ = 0`. -/
theorem fixedP506L0_U5_occurrenceTemporal_scalarFirstJet_eq_recentered
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    holonomicScalarCovariantDerivative
        (U5OccurrenceTemporal (canonicalCauchySlicePoint time space)) 0 =
      holonomicScalarCovariantDerivative
        (RecenteredU5 (canonicalCauchySlicePoint time space)) 0 := by
  apply u5OccurrenceTemporal_scalarFirstJet_eq_recentered
  exact
    canonicalTimeSecondPrimitive_hasFDerivAt_zero_of_contDiffAt
      (U5OccurrenceAcceleration
        (canonicalCauchySlicePoint time space))
      (fixedP506L0_U5_occurrenceAcceleration_contDiffAt
        time space inDomain)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
