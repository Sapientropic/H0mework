import H0mework.Versions.R2.Physics.MotherProgrammesFormationClockBF.Action
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.NativeSource
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.NativeHistory

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFPreparation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField SU7MotherLieAlgebra
open StageNineBlockwiseConstitutive StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineDiracDualFormNativeMotherAction
open StageNineP286SourceNativeCenteredReducedEntropyIteration
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous Stage9C.Revision
open ClockBF
open scoped ContDiff

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance p286CoordinateFintype : Fintype P286CoordinateIndex := Fintype.ofFinite _

theorem configuration_coframe (u b : ℝ) :
    (clockBFConfiguration u b).coframe = fun _ => homogeneousCoframe ((1 + u) * lapse) := by
  funext point row column
  simp only [clockBFConfiguration, Runtime.configuration_eq, actual_coframe]
  fin_cases row <;> fin_cases column <;>
    simp [homogeneousCoframe, StageNineP286ActionCauchySplit.canonicalLorentzianTimeDirection]

theorem configuration_connection (u b : ℝ) :
    (clockBFConfiguration u b).gaugeConnection = fun _ => gaugePotential gaugeScale := by
  change Runtime.configuration.gaugeConnection = _
  rw [Runtime.configuration_eq, actual_gaugeConnection]

theorem configuration_curvature (u b : ℝ) (point : BasePoint) :
    holonomicGaugeCurvature (clockBFConfiguration u b) point = magneticCurvature gaugeScale :=
  constantGauge_curvature _ _ (configuration_connection u b) point

theorem configuration_auxiliary (u b : ℝ) :
    (clockBFConfiguration u b).gaugeAuxiliary =
      fun _ => (1 + b) • electricAuxiliary lapse gaugeScale := by
  change (fun point => (1 + b) • Runtime.configuration.gaugeAuxiliary point) = _
  rw [Runtime.configuration_eq, actual_gaugeAuxiliary]

private theorem homogeneous_inverse (clock : ℝ) (nonzero : clock ≠ 0) :
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (homogeneousCoframe clock) (magneticCurvature gaugeScale) =
      electricAuxiliary clock gaugeScale := by
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary formNativeP286LiftedCoframeHodge
  rw [homogeneousHodge_lift clock nonzero]
  funext pair
  fin_cases pair <;>
    simp [formNativeP286BlockScale, magneticCurvature, electricAuxiliary,
      sourceColorP286Generator_weak_zero, sourceColorP286Generator_hypercharge_zero,
      sourceCoupling, smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  all_goals
    apply Prod.ext
    · rfl
    · apply Prod.ext <;>
        simp [sourceColorP286Generator_weak_zero, sourceColorP286Generator_hypercharge_zero]

private theorem electric_clock_scaled (u : ℝ) (positive : 0 < 1 + u) :
    electricAuxiliary ((1 + u) * lapse) gaugeScale =
      (1 + generatedB u) • electricAuxiliary lapse gaugeScale := by
  have coefficient : gaugeScale ^ 2 / (sourceCoupling * ((1 + u) * lapse)) =
      (1 + generatedB u) * (gaugeScale ^ 2 / (sourceCoupling * lapse)) := by
    rw [sourceCoupling_eq]
    unfold generatedB
    field_simp [ne_of_gt positive, ne_of_gt lapse_pos]
    ring
  funext pair
  fin_cases pair <;> simp [electricAuxiliary, smul_smul, coefficient]

/-- The positive clock factor keeps the original time orientation and
nondegenerate local coframe. It is a parameter domain, not a reality gate. -/
theorem constitutive_update (u b : ℝ) (positive : 0 < 1 + u) :
    formNativeP286GaugeConstitutiveReadout Runtime.source (clockBFConfiguration u b) =
      clockBFConfiguration u (generatedB u) := by
  rw [Runtime.source_eq]
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  funext point
  rw [formNativeP286GaugeConstitutiveReadout_gaugeAuxiliary, configuration_coframe,
    configuration_curvature, configuration_auxiliary,
    homogeneous_inverse _ (ne_of_gt (mul_pos positive lapse_pos)), electric_clock_scaled u positive]

theorem configuration_smooth (u b : ℝ) : (clockBFConfiguration u b).Smooth := by
  obtain ⟨_, connection, gravityAuxiliary, multiplier, gaugeConnection, _, scalar, matter, dual⟩ :=
    Recovery.stageOneThroughTenClosure.final.classical.smooth
  refine ⟨?_, connection, gravityAuxiliary, multiplier, gaugeConnection, ?_, scalar, matter, dual⟩
  · intro row column
    rw [configuration_coframe]
    exact contDiff_const
  · intro pair
    rw [configuration_auxiliary]
    exact contDiff_const

theorem configuration_det (u b : ℝ) (point : BasePoint) :
    Matrix.det ((clockBFConfiguration u b).coframe point) = (1 + u) * lapse := by
  rw [configuration_coframe, homogeneousCoframe_det]

theorem configuration_nondegenerate (u b : ℝ) (positive : 0 < 1 + u) :
    (clockBFConfiguration u b).Nondegenerate := by
  intro point
  rw [configuration_det]
  exact ne_of_gt (mul_pos positive lapse_pos)

/-- The old constitutive producer computes the entire qualified operand;
its auxiliary equation is an output of that producer. -/
def prepared (u : ℝ) (positive : 0 < 1 + u) : MaterialState :=
  ActualSourceCoverage.preparedState (clockBFConfiguration u 0)
    (configuration_smooth u 0) (configuration_nondegenerate u 0 positive)

theorem prepared_current (u : ℝ) (positive : 0 < 1 + u) :
    (prepared u positive).current = clockBFConfiguration u (generatedB u) := by
  change formNativeP286GaugeConstitutiveReadout positiveSmoothUnifiedSource (clockBFConfiguration u 0) = _
  simpa only [Runtime.source_eq] using constitutive_update u 0 positive

theorem prepared_action (u : ℝ) (positive : 0 < 1 + u) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity motherSource 0 0
      (toContinuumPointField (prepared u positive).current 0) = effectiveClockAction u := by
  rw [prepared_current]
  exact generatedB_action u positive

set_option maxHeartbeats 2000000 in
theorem native_consumed (u : ℝ) (positive : 0 < 1 + u) (step : ℕ) :
    let current := NativeFamily.stateAt (prepared u positive) step
    let successor := NativeFamily.successorAt (prepared u positive) step
    SpinPair.source.toRootSource.actual.compile
        (NativeFamily.occurrenceAt (prepared u positive) step) =
      .nativeWrite (materialActionAt (SpinPair.underlying (.running current))) ∧
    successor.targetCurrent = (NativeFamily.visitAt (prepared u positive) (step + 1)).current ∧
    Recognition.wholeField successor.targetCurrent =
      Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource current.current
        current.smooth current.nondegenerate 0 ∧
    successor.ledgerEvolution.destination (materialEntry (SpinPair.support (.running current))) =
      ⟨materialEntry (SpinPair.support (NativeFamily.visitAt (prepared u positive) (step + 1)).current),
        .transferred (.transfer (materialActionAt (SpinPair.underlying (.running current))))
          rfl rfl (Nat.le_refl _)⟩ :=
  NativeFamily.next_consumed (prepared u positive) step

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFPreparation
