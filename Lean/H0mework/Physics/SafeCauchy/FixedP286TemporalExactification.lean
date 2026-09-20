import H0mework.Physics.SafeCauchy.FixedJointGlobalECJetRegularity
import H0mework.Physics.JointVariation.P286TemporalDevelopmentOperator

/-!
# SafeFinal source-native P286 temporal exactification candidate

The active SafeFinal P286 leg currently integrates a four-dimensional
first-jet one-form radially.  That construction is exact at the source
contact, but away from it retains the genuine Poincare antisymmetry defect.

This bounded candidate uses the already-defined Cauchy temporal homotopy on
the *same* source and exact constitutive stage.  It generates one global
auxiliary two-form and realizes, at every spacetime point, all three exterior
coordinates containing the canonical time direction.  Full exterior
settlement is thereby equivalent to the sole spatial `123` Gauss row.

No residual, Ward zero, stationarity law, target field, or branch is an input.
The file does not yet replace the active radial leg; it is the compiled
producer/consumer contract for that later single-leg substitution.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeP286TemporalExactification

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalTimePrimitiveSegmentRegularity
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalFourFormPairing
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance temporalExactificationP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance temporalExactificationP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Current : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

private abbrev GlobalTemporal : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalTemporalCurrent Source Current

private abbrev GlobalConstitutive : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalConstitutiveCurrent Source Current

/-- The bounded replacement candidate: the existing source/current-only
Cauchy temporal homotopy, applied to the exact SafeFinal constitutive stage. -/
def fixedP506L0CartanECConstraintCauchySafeP286TemporalExactificationActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator
    Source GlobalConstitutive

private abbrev TemporalP286 : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeP286TemporalExactificationActual

private theorem globalConstitutive_eq_constitutiveReadout :
    GlobalConstitutive =
      formNativeP286GaugeConstitutiveReadout Source GlobalTemporal :=
  rfl

private theorem zeroSliceProjection_contDiff :
    ContDiff ℝ ∞ (fun point : BasePoint =>
      canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) := by
  have zeroSlice : ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
    rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
      funext space
      rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
      simp]
    exact canonicalSpatialInclusion.contDiff
  exact zeroSlice.comp canonicalSpatialProjection.contDiff

private theorem anchorCoordinate_eq_constitutiveZeroSlice :
    holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286ZeroSliceAnchoredCurrent Source GlobalConstitutive) =
      fun point =>
        holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) := by
  funext point
  unfold completeJointP286ZeroSliceAnchoredCurrent
    holonomicP286GaugeAuxiliaryCoordinate
  simp only [p286CoordinateEquiv.apply_symm_apply]
  rw [globalConstitutive_eq_constitutiveReadout]
  exact completeJointP286ZeroSliceAnchor_constitutiveReadout Source
    GlobalTemporal (canonicalSpatialProjection point)

private theorem globalConstitutive_auxiliaryCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive) := by
  apply contDiff_pi'
  intro pair
  exact
    fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_smooth.2.2.2.2.2.1
      pair

private theorem anchorCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate
        (completeJointP286ZeroSliceAnchoredCurrent Source
          GlobalConstitutive)) := by
  rw [anchorCoordinate_eq_constitutiveZeroSlice]
  exact globalConstitutive_auxiliaryCoordinate_contDiff.comp
    zeroSliceProjection_contDiff

private theorem auxiliaryExteriorDerivative_contDiff_of_coordinate
    (configuration : StageNineHolonomicConfiguration)
    (coordinateRegular :
      ContDiff ℝ ∞
        (holonomicP286GaugeAuxiliaryCoordinate configuration)) :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryExteriorDerivative configuration) := by
  have firstJetRegular : ContDiff ℝ ∞
      (fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate configuration)) :=
    coordinateRegular.fderiv_right (by simp)
  have directionalRegular (direction : LorentzianIndex) :
      ContDiff ℝ ∞ (fun point =>
        p286GaugeAuxiliaryDirectionalDerivative configuration point
          direction) := by
    unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
    exact firstJetRegular.clm_apply contDiff_const
  have orderedRegular (direction first second : LorentzianIndex) :
      ContDiff ℝ ∞ (fun point =>
        orderedP286GaugeTwoFormComponent
          (p286GaugeAuxiliaryDirectionalDerivative configuration point
            direction) first second) := by
    unfold orderedP286GaugeTwoFormComponent
    apply ContDiff.sum
    intro pair _
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
      orientedLorentzBivectorBasisCoefficient pair first second)).smul
        (contDiff_pi.mp (directionalRegular direction) pair)
  apply contDiff_pi'
  intro triple
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
  exact
    ((orderedRegular (threeFormFirst triple) (threeFormSecond triple)
        (threeFormThird triple)).add
      (orderedRegular (threeFormSecond triple) (threeFormThird triple)
        (threeFormFirst triple))).add
      (orderedRegular (threeFormThird triple) (threeFormFirst triple)
        (threeFormSecond triple))

private theorem anchorExteriorDerivative_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryExteriorDerivative
        (completeJointP286ZeroSliceAnchoredCurrent Source
          GlobalConstitutive)) :=
  auxiliaryExteriorDerivative_contDiff_of_coordinate _ anchorCoordinate_contDiff

private theorem temporalCorrectionProfile_contDiff :
    ContDiff ℝ ∞
      (completeJointP286TemporalCorrectionProfile Source
        GlobalConstitutive) := by
  apply contDiff_pi'
  intro pair
  fin_cases pair
  · simpa [completeJointP286TemporalCorrectionProfile,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      canonicalLorentzianTimeDirection] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
        (0 : P286CoordinateCarrier)))
  · simpa [completeJointP286TemporalCorrectionProfile,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      canonicalLorentzianTimeDirection] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
        (0 : P286CoordinateCarrier)))
  · simpa [completeJointP286TemporalCorrectionProfile,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      canonicalLorentzianTimeDirection] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
        (0 : P286CoordinateCarrier)))
  · simpa [completeJointP286TemporalCorrectionProfile,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      canonicalLorentzianTimeDirection] using
      (contDiff_pi.mp
        (fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_requiredExterior_contDiff.sub
          anchorExteriorDerivative_contDiff) 2)
  · simpa [completeJointP286TemporalCorrectionProfile,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      canonicalLorentzianTimeDirection] using
      (contDiff_pi.mp
        (fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_requiredExterior_contDiff.sub
          anchorExteriorDerivative_contDiff) 1).neg
  · simpa [completeJointP286TemporalCorrectionProfile,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      canonicalLorentzianTimeDirection] using
      (contDiff_pi.mp
        (fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_requiredExterior_contDiff.sub
          anchorExteriorDerivative_contDiff) 0)

private theorem canonicalTimePrimitive_contDiff_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (profile : BasePoint → E) (regular : ContDiff ℝ ∞ profile) :
    ContDiff ℝ ∞ (canonicalTimePrimitive profile) := by
  rw [contDiff_infty]
  intro order
  rw [contDiff_iff_contDiffAt]
  intro point
  apply canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment_finite
    order profile Set.univ isOpen_univ
  · exact (regular.of_le
      (show ((((order + 1 : ℕ) : ℕ∞)) : ℕ∞ω) ≤
          ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top)).contDiffOn
  · simp

private theorem temporalP286_auxiliaryCoordinate_apply
    (point : BasePoint) (pair : Fin 6) :
    holonomicP286GaugeAuxiliaryCoordinate TemporalP286 point pair =
      holonomicP286GaugeAuxiliaryCoordinate
          (completeJointP286ZeroSliceAnchoredCurrent Source
            GlobalConstitutive) point pair +
        canonicalTimePrimitive
          (fun candidate =>
            completeJointP286TemporalCorrectionProfile Source
              GlobalConstitutive candidate pair) point := by
  simp [TemporalP286,
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactificationActual,
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator,
    completeJointP286TemporalCorrectionPrimitive,
    completeJointP286ZeroSliceAnchoredCurrent,
    holonomicP286GaugeAuxiliaryCoordinate, canonicalTimePrimitive]

/-- The alternative P286 output is a globally smooth auxiliary field; this
discharges all analytic premises of the existing temporal homotopy theorem. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_auxiliaryCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate TemporalP286) := by
  apply contDiff_pi'
  intro pair
  rw [show (fun point =>
      holonomicP286GaugeAuxiliaryCoordinate TemporalP286 point pair) =
      fun point =>
        holonomicP286GaugeAuxiliaryCoordinate
            (completeJointP286ZeroSliceAnchoredCurrent Source
              GlobalConstitutive) point pair +
          canonicalTimePrimitive
            (fun candidate =>
              completeJointP286TemporalCorrectionProfile Source
                GlobalConstitutive candidate pair) point by
    funext point
    exact temporalP286_auxiliaryCoordinate_apply point pair]
  exact (contDiff_pi.mp anchorCoordinate_contDiff pair).add
    (canonicalTimePrimitive_contDiff_of_contDiff _
      (contDiff_pi.mp temporalCorrectionProfile_contDiff pair))

private theorem correction_timeLine_continuous
    (space : StageNineSpatialPoint) (pair : Fin 6) :
    Continuous (fun time : ℝ =>
      completeJointP286TemporalCorrectionProfile Source GlobalConstitutive
        (canonicalCauchySlicePoint time space) pair) := by
  have lineRegular : ContDiff ℝ ∞
      (fun time : ℝ => canonicalCauchySlicePoint time space) := by
    let timeLinear : ℝ →L[ℝ] BasePoint :=
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (coordinateDirection canonicalLorentzianTimeDirection)
    rw [show (fun time : ℝ => canonicalCauchySlicePoint time space) =
        fun time => canonicalSpatialInclusion space + timeLinear time by
      funext time
      apply PiLp.ext
      intro direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, canonicalSpatialInclusion,
          canonicalSpatialCoordinate, canonicalLorentzianTimeDirection,
          coordinateDirection, timeLinear, Fin.sum_univ_three]]
    exact contDiff_const.add timeLinear.contDiff
  exact (contDiff_pi.mp temporalCorrectionProfile_contDiff pair).continuous.comp
    lineRegular.continuous

/-- All three time-containing pure-exterior coordinates are generated at
every spacetime point by the same source/current occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_exteriorDerivative_temporal
    (point : BasePoint) (triple : Fin 4) (temporal : triple ≠ 3) :
    holonomicP286GaugeAuxiliaryExteriorDerivative TemporalP286 point triple =
      completeJointP286RequiredExteriorProfile Source GlobalConstitutive
        point triple := by
  let time := canonicalTimeProjection point
  let space := canonicalSpatialProjection point
  have pointEq : canonicalCauchySlicePoint time space = point :=
    canonicalCauchySlicePoint_projections point
  rw [← pointEq]
  apply
    sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_exteriorDerivative_temporal
      Source GlobalConstitutive space time triple temporal
      fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_auxiliaryCoordinate_contDiff
      anchorCoordinate_contDiff
  · intro pair
    exact (correction_timeLine_continuous space pair).intervalIntegrable 0 time
  · intro pair
    exact (correction_timeLine_continuous space pair
      ).stronglyMeasurableAtFilter MeasureTheory.volume (nhds time)
  · intro pair
    exact (correction_timeLine_continuous space pair).continuousAt

/-- Full pure-exterior settlement is *exactly* the one remaining spatial
`123` Gauss row.  This is the bounded candidate's direct consumer. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_fullExterior_iff_spatial123 :
    (∀ point : BasePoint,
      holonomicP286GaugeAuxiliaryExteriorDerivative TemporalP286 point =
        completeJointP286RequiredExteriorProfile Source GlobalConstitutive
          point) ↔
      ∀ point : BasePoint,
        holonomicP286GaugeAuxiliaryExteriorDerivative TemporalP286 point 3 =
          completeJointP286RequiredExteriorProfile Source GlobalConstitutive
            point 3 := by
  constructor
  · intro full point
    exact congrFun (full point) 3
  · intro spatial point
    funext triple
    fin_cases triple
    · exact
        fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_exteriorDerivative_temporal
          point 0 (by decide)
    · exact
        fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_exteriorDerivative_temporal
          point 1 (by decide)
    · exact
        fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_exteriorDerivative_temporal
          point 2 (by decide)
    · exact spatial point

/-! ## Direct Euler-residual consumer

The temporal homotopy settles the pure exterior principal exactly.  The full
non-Abelian Euler row additionally rereads `[A,B]` on the newly generated
auxiliary.  We retain that honest same-occurrence changed read below instead
of silently treating a pure exterior equality as a full field equation.
-/

/-- Nonlinear connection read changed by this exact temporal P286 write. -/
def fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
    (point : BasePoint) : P286GaugeThreeForm :=
  pointwiseP286GaugeTwoFormConnectionExteriorAction
      (holonomicP286GaugeConnectionCoordinate GlobalConstitutive point)
      (holonomicP286GaugeAuxiliaryCoordinate TemporalP286 point) -
    pointwiseP286GaugeTwoFormConnectionExteriorAction
      (holonomicP286GaugeConnectionCoordinate GlobalConstitutive point)
      (holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive point)

private theorem temporalP286_chargedThreeForm_eq_constitutive
    (point : BasePoint) :
    formNativeChargedGaugeThreeForm Source 0 point
        (toContinuumPointField TemporalP286 point) =
      formNativeChargedGaugeThreeForm Source 0 point
        (toContinuumPointField GlobalConstitutive point) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem requiredExterior_eq_direct (point : BasePoint) :
    completeJointP286RequiredExteriorProfile Source GlobalConstitutive point =
      pointwiseDirectP286RequiredExteriorDerivative Source
        GlobalConstitutive point :=
  completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
    Source GlobalConstitutive point
      (fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_constitutiveAt
        point)

/-- Exact full-Euler normal form for each of the three generated temporal
coordinates.  The pure exterior term is gone; the only remaining term is the
nonlinear `[A,B]` reread of this same write. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
    (point : BasePoint) (triple : Fin 4) (temporal : triple ≠ 3) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286 point
        triple =
      fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
        point triple := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  simp only [Pi.add_apply]
  rw [show
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative TemporalP286 point
        triple =
      holonomicP286GaugeAuxiliaryExteriorDerivative TemporalP286 point triple +
        pointwiseP286GaugeTwoFormConnectionExteriorAction
          (holonomicP286GaugeConnectionCoordinate TemporalP286 point)
          (holonomicP286GaugeAuxiliaryCoordinate TemporalP286 point) triple by
    exact congrFun
      (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts
        TemporalP286 point) triple]
  rw [fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_exteriorDerivative_temporal
    point triple temporal]
  rw [requiredExterior_eq_direct]
  unfold pointwiseDirectP286RequiredExteriorDerivative
    formNativePhysicalChargedGaugeCurrentThreeForm
    fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
  rw [show holonomicP286GaugeConnectionCoordinate TemporalP286 point =
      holonomicP286GaugeConnectionCoordinate GlobalConstitutive point by rfl]
  rw [temporalP286_chargedThreeForm_eq_constitutive]
  simp only [Pi.sub_apply, Pi.neg_apply]
  abel

/-- Whole temporal part of the full Euler row is settled exactly when the
same-write nonlinear reread vanishes on the three time-containing
coordinates.  This is the direct residual consumer needed before installation
into the total lock. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_eulerTemporal_zero_iff_changedRead :
    (∀ point : BasePoint, ∀ triple : Fin 4, triple ≠ 3 →
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286 point
        triple = 0) ↔
      ∀ point : BasePoint, ∀ triple : Fin 4, triple ≠ 3 →
        fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
          point triple = 0 := by
  constructor <;> intro hypothesis point triple temporal
  · rw [← fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
      point triple temporal]
    exact hypothesis point triple temporal
  · rw [fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
      point triple temporal]
    exact hypothesis point triple temporal

/-- On the source-generated initial slice the temporal homotopy starts from
the literal constitutive auxiliary of the same occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_auxiliary_zeroSlice_eq_constitutive
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate TemporalP286
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive
        (canonicalCauchySlicePoint 0 space) := by
  calc
    holonomicP286GaugeAuxiliaryCoordinate TemporalP286
          (canonicalCauchySlicePoint 0 space) =
        completeJointP286ZeroSliceAnchor Source GlobalConstitutive space := by
      exact
        sourceActionGeneratedDiracDualCompleteJointP286TemporalDevelopmentOperator_gaugeAuxiliary_zeroSlice
          Source GlobalConstitutive space
    _ = holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive
          (canonicalCauchySlicePoint 0 space) := by
      rw [globalConstitutive_eq_constitutiveReadout]
      exact completeJointP286ZeroSliceAnchor_constitutiveReadout Source
        GlobalTemporal space

/-- Consequently the honest nonlinear reread vanishes on the complete
initial slice; no fixed-point premise is needed there. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
        (canonicalCauchySlicePoint 0 space) = 0 := by
  unfold
    fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
  rw [fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_auxiliary_zeroSlice_eq_constitutive]
  exact sub_self _

/-- The three full non-Abelian Euler coordinates containing time vanish on
every point of the generated initial slice. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_zeroSlice
    (space : StageNineSpatialPoint) (triple : Fin 4) (temporal : triple ≠ 3) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286
        (canonicalCauchySlicePoint 0 space) triple = 0 := by
  rw [fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
    (canonicalCauchySlicePoint 0 space) triple temporal]
  rw [fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead_zeroSlice]
  rfl

/-- Exact initial-constraint boundary: after the source-native temporal
write, full P286 Euler settlement on the complete Cauchy slice is equivalent
to the one spatial `123` Gauss row. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_zeroSlice_iff_spatial123 :
    (∀ space : StageNineSpatialPoint,
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286
        (canonicalCauchySlicePoint 0 space) = 0) ↔
      ∀ space : StageNineSpatialPoint,
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286
          (canonicalCauchySlicePoint 0 space) 3 = 0 := by
  constructor
  · intro full space
    simpa only [Pi.zero_apply] using congrFun (full space) 3
  · intro spatial space
    funext triple
    fin_cases triple
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286
          (canonicalCauchySlicePoint 0 space) 0 = 0
      exact
        fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_zeroSlice
          space 0 (by decide)
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286
          (canonicalCauchySlicePoint 0 space) 1 = 0
      exact
        fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_zeroSlice
          space 1 (by decide)
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286
          (canonicalCauchySlicePoint 0 space) 2 = 0
      exact
        fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_zeroSlice
          space 2 (by decide)
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286
          (canonicalCauchySlicePoint 0 space) 3 = 0
      exact spatial space

/-- Exhaustive pointwise reduction of the candidate's full P286 Euler row:
three nonlinear temporal rereads plus the single spatial `123` Gauss row. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_zero_iff_temporalChangedRead_and_spatial123
    (point : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286 point = 0
      ↔
      fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
          point 0 = 0 ∧
        fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
          point 1 = 0 ∧
        fixedP506L0CartanECConstraintCauchySafeP286TemporalNonlinearChangedRead
          point 2 = 0 ∧
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286 point
          3 = 0 := by
  constructor
  · intro residualZero
    have coordinateZero (triple : Fin 4) := congrFun residualZero triple
    have zero0 := coordinateZero 0
    have zero1 := coordinateZero 1
    have zero2 := coordinateZero 2
    rw [fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
      point 0 (by decide)] at zero0
    rw [fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
      point 1 (by decide)] at zero1
    rw [fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
      point 2 (by decide)] at zero2
    exact ⟨by simpa only [Pi.zero_apply] using zero0,
      by simpa only [Pi.zero_apply] using zero1,
      by simpa only [Pi.zero_apply] using zero2,
      by simpa only [Pi.zero_apply] using coordinateZero 3⟩
  · rintro ⟨zero0, zero1, zero2, zero3⟩
    funext triple
    fin_cases triple
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286 point
          0 = 0
      exact
        (fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
          point 0 (by decide)).trans zero0
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286 point
          1 = 0
      exact
        (fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
          point 1 (by decide)).trans zero1
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286 point
          2 = 0
      exact
        (fixedP506L0CartanECConstraintCauchySafeP286TemporalExactification_euler_temporal_eq_changedRead
          point 2 (by decide)).trans zero2
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 TemporalP286 point
          3 = 0
      exact zero3

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeP286TemporalExactification
end PhysicsCore
end SaturationMonoid
