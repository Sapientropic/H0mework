import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCurrentComplexMatrix

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentConstrainedInverse
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open scoped BigOperators Matrix
attribute [local irreducible] sourceCurrentUpdateMatrix sourceCurrentMatrix originalJacobi sourceGreen sourceCompatibility
  sourceCommonUpdateOperator sourceLaplaceCurrent sourceLaplaceInitial sourceCausalHalfOperator sourceComplexCommonUpdate

abbrev SourceCurrentFrequency (q : PhysicalResponsePoint) (clock : ℂ) :=
  {lambda : physicalSpectralDomain q.k | sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.val.re}

def sourceFeedbackMatrix (q : PhysicalResponsePoint) (clock : ℂ) (frequency : SourceCurrentFrequency q clock) :
    Matrix (Fin 289) (Fin 289) ℂ:=1-sourceCurrentUpdateMatrix q clock frequency.val frequency.property

def sourceFeedbackDenominator (q : PhysicalResponsePoint) (clock : ℂ) (frequency : SourceCurrentFrequency q clock) : ℂ:=
  (sourceFeedbackMatrix q clock frequency).det

def sourceFeedbackAdjugate (q : PhysicalResponsePoint) (clock : ℂ) (frequency : SourceCurrentFrequency q clock) :
    Matrix (Fin 289) (Fin 289) ℂ:=(sourceFeedbackMatrix q clock frequency).adjugate

theorem sourceFeedbackAdjugate_left (q : PhysicalResponsePoint) (clock : ℂ) (frequency : SourceCurrentFrequency q clock) :
    sourceFeedbackAdjugate q clock frequency*sourceFeedbackMatrix q clock frequency=
      sourceFeedbackDenominator q clock frequency • (1 : Matrix (Fin 289) (Fin 289) ℂ) :=
  Matrix.adjugate_mul _

theorem sourceFeedbackAdjugate_right (q : PhysicalResponsePoint) (clock : ℂ) (frequency : SourceCurrentFrequency q clock) :
    sourceFeedbackMatrix q clock frequency*sourceFeedbackAdjugate q clock frequency=
      sourceFeedbackDenominator q clock frequency • (1 : Matrix (Fin 289) (Fin 289) ℂ) :=
  Matrix.mul_adjugate _

attribute [local irreducible] sourceFeedbackDenominator sourceFeedbackMatrix

/-- The spectral exceptional set belongs to the actual history-current update matrix. -/
def sourceCurrentRegularDomain (q : PhysicalResponsePoint) (clock : ℂ) : Set (SourceCurrentFrequency q clock):=
  {frequency | sourceFeedbackDenominator q clock frequency≠0}

def sourceFeedbackResolvent (q : PhysicalResponsePoint) (clock : ℂ) (frequency : SourceCurrentFrequency q clock) :
    Matrix (Fin 289) (Fin 289) ℂ:=
  (sourceFeedbackDenominator q clock frequency)⁻¹ • sourceFeedbackAdjugate q clock frequency

attribute [local irreducible] sourceFeedbackResolvent

theorem sourceFeedbackResolvent_left (q : PhysicalResponsePoint) (clock : ℂ)
    (frequency : sourceCurrentRegularDomain q clock) :
    sourceFeedbackResolvent q clock frequency.val*sourceFeedbackMatrix q clock frequency.val=1 :=by
  rw [sourceFeedbackResolvent,Matrix.smul_mul,sourceFeedbackAdjugate_left,smul_smul,
    inv_mul_cancel₀ frequency.property,one_smul]

theorem sourceFeedbackResolvent_right (q : PhysicalResponsePoint) (clock : ℂ)
    (frequency : sourceCurrentRegularDomain q clock) :
    sourceFeedbackMatrix q clock frequency.val*sourceFeedbackResolvent q clock frequency.val=1 :=by
  rw [sourceFeedbackResolvent,Matrix.mul_smul,sourceFeedbackAdjugate_right,smul_smul,
    inv_mul_cancel₀ frequency.property,one_smul]

theorem sourceFeedbackMatrix_actual (q : PhysicalResponsePoint) (clock : ℂ)
    (frequency : SourceCurrentFrequency q clock) (field : SignalAmplitude) :
    sourceFeedbackMatrix q clock frequency*ᵥfield=
      field-sourceCommonUpdateOperator q clock frequency.val field :=by
  rw [sourceFeedbackMatrix,Matrix.sub_mulVec,Matrix.one_mulVec,sourceCurrentUpdateMatrix_actual]

theorem sourceFeedbackResponse_generated (q : PhysicalResponsePoint) (clock : ℂ)
    (frequency : sourceCurrentRegularDomain q clock) (forcing : SignalAmplitude) :
    sourceFeedbackResolvent q clock frequency.val*ᵥforcing=
      forcing+sourceCommonUpdateOperator q clock frequency.val.val
        (sourceFeedbackResolvent q clock frequency.val*ᵥforcing) :=by
  have actual:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A*ᵥforcing)
    (sourceFeedbackResolvent_right q clock frequency)
  rw [←Matrix.mulVec_mulVec,Matrix.one_mulVec,sourceFeedbackMatrix_actual] at actual
  exact sub_eq_iff_eq_add.mp actual

theorem sourceFeedbackResponse_unique (q : PhysicalResponsePoint) (clock : ℂ)
    (frequency : sourceCurrentRegularDomain q clock) (forcing field : SignalAmplitude)
    (equation : field=forcing+sourceCommonUpdateOperator q clock frequency.val.val field) :
    field=sourceFeedbackResolvent q clock frequency.val*ᵥforcing :=by
  have residual : sourceFeedbackMatrix q clock frequency.val*ᵥfield=forcing :=by
    rw [sourceFeedbackMatrix_actual]
    exact sub_eq_iff_eq_add.mpr equation
  have transported:=congrArg (fun v : SignalAmplitude=>sourceFeedbackResolvent q clock frequency.val*ᵥv) residual
  rw [Matrix.mulVec_mulVec,sourceFeedbackResolvent_left,Matrix.one_mulVec] at transported
  exact transported

end LowEnergy.PreparationVacuumCurrentConstrainedInverse
