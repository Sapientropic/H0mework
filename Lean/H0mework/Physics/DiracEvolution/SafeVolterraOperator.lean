import H0mework.Physics.DiracEvolution.SafeDifferentialOperator
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterVolterra

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCauchySafeMatterDifferentialOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false

/-- Action-native coordinate velocity reread from one candidate on a fixed
background current. -/
def cauchySafeMatterVolterraVelocity
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv
    (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
      (cauchySafeMatterCandidateActual current candidate) point)

private theorem cauchySafeMatterCandidate_knownVector_add
    (current : StageNineHolonomicConfiguration)
    (first second : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (firstDifferentiable :
      DifferentiableAt ℝ
        (fun candidate ↦ matterCoordinateEquiv (first candidate)) point)
    (secondDifferentiable :
      DifferentiableAt ℝ
        (fun candidate ↦ matterCoordinateEquiv (second candidate)) point) :
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (cauchySafeMatterCandidateActual current (first + second)) point =
      holonomicDiracDualCurrentCoframeMatterKnownVector
          (cauchySafeMatterCandidateActual current first) point +
        holonomicDiracDualCurrentCoframeMatterKnownVector
          (cauchySafeMatterCandidateActual current second) point := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  simp_rw [cauchySafeMatterCandidate_covariantDerivative_add current first
    second point firstDifferentiable secondDifferentiable]
  unfold cauchySafeMatterCandidateActual
  simp only [Pi.add_apply, map_add, Finset.sum_add_distrib, smul_add]
  abel

private theorem cauchySafeMatterCandidate_knownVector_real_smul
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (parameter : ℝ)
    (point : BasePoint)
    (candidateDifferentiable :
      DifferentiableAt ℝ
        (fun position ↦ matterCoordinateEquiv (candidate position)) point) :
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (cauchySafeMatterCandidateActual current (parameter • candidate))
        point =
      parameter •
        holonomicDiracDualCurrentCoframeMatterKnownVector
          (cauchySafeMatterCandidateActual current candidate) point := by
  change
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (cauchySafeMatterCandidateActual current (parameter • candidate))
        point =
      (parameter : ℂ) •
        holonomicDiracDualCurrentCoframeMatterKnownVector
          (cauchySafeMatterCandidateActual current candidate) point
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  simp_rw [cauchySafeMatterCandidate_covariantDerivative_real_smul current
    candidate parameter point candidateDifferentiable]
  unfold cauchySafeMatterCandidateActual
  simp only [Pi.smul_apply, diracMatrixMatterAction_real_smul]
  let spatialTerm : Fin 3 → DiracExteriorMatterCarrier := fun direction ↦
    diracMatrixMatterAction
      (inverseCoframeDiracGamma
        { coframe := current.coframe point, derivative := 0 }
        direction.succ)
      (holonomicMatterCovariantDerivative
        (cauchySafeMatterCandidateActual current candidate) point
        direction.succ)
  let yukawa :=
    diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (current.scalar point))
  change
    Complex.I • (∑ direction, (parameter : ℂ) • spatialTerm direction) +
        yukawa ((parameter : ℂ) • candidate point) =
      (parameter : ℂ) •
        (Complex.I • (∑ direction, spatialTerm direction) +
          yukawa (candidate point))
  rw [← Finset.smul_sum, map_smul]
  module

/-- The action-native coordinate velocity preserves addition of candidate
sections at their common differentiability point. -/
theorem cauchySafeMatterVolterraVelocity_add
    (current : StageNineHolonomicConfiguration)
    (first second : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (firstDifferentiable :
      DifferentiableAt ℝ
        (fun candidate ↦ matterCoordinateEquiv (first candidate)) point)
    (secondDifferentiable :
      DifferentiableAt ℝ
        (fun candidate ↦ matterCoordinateEquiv (second candidate)) point) :
    cauchySafeMatterVolterraVelocity current (first + second) point =
      cauchySafeMatterVolterraVelocity current first point +
        cauchySafeMatterVolterraVelocity current second point := by
  unfold cauchySafeMatterVolterraVelocity
  rw [← matterCoordinateEquiv.map_add]
  apply congrArg matterCoordinateEquiv
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
  rw [cauchySafeMatterCandidate_knownVector_add current first second point
    firstDifferentiable secondDifferentiable]
  unfold holonomicMatterConnectionAction cauchySafeMatterCandidateActual
  simp only [Pi.add_apply, map_add]
  abel

/-- The action-native coordinate velocity commutes with real scalar
multiplication of a candidate section at every differentiability point. -/
theorem cauchySafeMatterVolterraVelocity_real_smul
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (parameter : ℝ)
    (point : BasePoint)
    (candidateDifferentiable :
      DifferentiableAt ℝ
        (fun position ↦ matterCoordinateEquiv (candidate position)) point) :
    cauchySafeMatterVolterraVelocity current (parameter • candidate) point =
      parameter •
        cauchySafeMatterVolterraVelocity current candidate point := by
  unfold cauchySafeMatterVolterraVelocity
  rw [← matterCoordinateEquiv_real_smul]
  apply congrArg matterCoordinateEquiv
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
  rw [cauchySafeMatterCandidate_knownVector_real_smul current candidate
    parameter point candidateDifferentiable]
  unfold holonomicMatterConnectionAction cauchySafeMatterCandidateActual
  simp only [Pi.smul_apply, diracMatrixMatterAction_real_smul,
    diracExteriorMotherLieAction_matter_real_smul]
  have inverseSmul (matter : DiracExteriorMatterCarrier) :
      currentCoframeMatterTemporalPrincipalInverse (current.coframe point)
          (parameter • matter) =
        parameter •
          currentCoframeMatterTemporalPrincipalInverse (current.coframe point)
            matter := by
    change
      currentCoframeMatterTemporalPrincipalInverse (current.coframe point)
          ((parameter : ℂ) • matter) =
        (parameter : ℂ) •
          currentCoframeMatterTemporalPrincipalInverse (current.coframe point)
            matter
    exact map_smul _ _ _
  rw [inverseSmul]
  module

/-- The Cauchy-anchored Volterra realization of a candidate's native temporal
velocity. -/
def cauchySafeMatterVolterraOperator
    (current : StageNineHolonomicConfiguration)
    (initial : StageNineSpatialPoint → DiracExteriorMatterCarrier)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  initial (canonicalSpatialProjection point) +
    matterCoordinateEquiv.symm
      (canonicalTimePrimitive
        (cauchySafeMatterVolterraVelocity current candidate) point)

theorem cauchySafeMatterVolterraOperator_zeroSlice
    (current : StageNineHolonomicConfiguration)
    (initial : StageNineSpatialPoint → DiracExteriorMatterCarrier)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (space : StageNineSpatialPoint) :
    cauchySafeMatterVolterraOperator current initial candidate
        (canonicalCauchySlicePoint 0 space) =
      initial space := by
  simp [cauchySafeMatterVolterraOperator]

theorem cauchySafeMatterVolterraOperator_coordinate_timeLine_hasDerivAt
    (current : StageNineHolonomicConfiguration)
    (initial : StageNineSpatialPoint → DiracExteriorMatterCarrier)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (index : MatterCoordinateIndex)
    (continuous :
      Continuous fun candidateTime ↦
        cauchySafeMatterVolterraVelocity current candidate
          (canonicalCauchySlicePoint candidateTime space)) :
    NormedHasDerivAt
      (fun candidateTime ↦
        matterCoordinateEquiv
          (cauchySafeMatterVolterraOperator current initial candidate
            (canonicalCauchySlicePoint candidateTime space)) index)
      (cauchySafeMatterVolterraVelocity current candidate
        (canonicalCauchySlicePoint time space) index)
      time := by
  have primitive :=
    canonicalTimePrimitive_timeLine_hasDerivAt
      (cauchySafeMatterVolterraVelocity current candidate) space time
      continuous
  let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) 2
      (fun _ : MatterCoordinateIndex => ℂ) index).restrictScalars ℝ
  have projected :=
    projection.hasFDerivAt.comp_hasDerivAt time primitive
  have primitiveCoordinate :
      NormedHasDerivAt
        (fun candidateTime ↦
          canonicalTimePrimitive
            (cauchySafeMatterVolterraVelocity current candidate)
            (canonicalCauchySlicePoint candidateTime space) index)
        (cauchySafeMatterVolterraVelocity current candidate
          (canonicalCauchySlicePoint time space) index)
        time := by
    convert projected using 1 <;> simp [projection, Function.comp_def]
  have fieldEq :
      (fun candidateTime ↦
        matterCoordinateEquiv
          (cauchySafeMatterVolterraOperator current initial candidate
            (canonicalCauchySlicePoint candidateTime space)) index) =
        fun candidateTime ↦
          matterCoordinateEquiv (initial space) index +
            canonicalTimePrimitive
              (cauchySafeMatterVolterraVelocity current candidate)
              (canonicalCauchySlicePoint candidateTime space) index := by
    funext candidateTime
    simp [cauchySafeMatterVolterraOperator]
  rw [fieldEq]
  exact primitiveCoordinate.const_add
    (matterCoordinateEquiv (initial space) index)

private theorem cauchySafeMatterVolterra_fixedPoint_operator_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (initial : StageNineSpatialPoint → DiracExteriorMatterCarrier)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (fixedPoint :
      candidate = cauchySafeMatterVolterraOperator current initial candidate)
    (candidateDifferentiable :
      DifferentiableAt ℝ
        (fun point ↦ matterCoordinateEquiv (candidate point))
        (canonicalCauchySlicePoint time space))
    (velocityContinuous :
      Continuous fun candidateTime ↦
        cauchySafeMatterVolterraVelocity current candidate
          (canonicalCauchySlicePoint candidateTime space))
    (noncharacteristic :
      coframeTemporalPrincipalScalar
        (current.coframe (canonicalCauchySlicePoint time space)) ≠ 0) :
    cauchySafeMatterDifferentialOperator source current candidate
        (canonicalCauchySlicePoint time space) = 0 := by
  let point := canonicalCauchySlicePoint time space
  have candidateTimeDerivative :=
    field_timeLine_hasDerivAt
      (fun point ↦ matterCoordinateEquiv (candidate point)) space time
      candidateDifferentiable
  have rawDerivativeCoordinatesEq :
      fieldDirectionalDerivative
          (fun point ↦ matterCoordinateEquiv (candidate point)) point
          canonicalLorentzianTimeDirection =
        cauchySafeMatterVolterraVelocity current candidate point := by
    apply PiLp.ext
    intro index
    let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
      (PiLp.proj (𝕜 := ℂ) 2
        (fun _ : MatterCoordinateIndex => ℂ) index).restrictScalars ℝ
    have candidateCoordinateDerivative :=
      projection.hasFDerivAt.comp_hasDerivAt time candidateTimeDerivative
    have candidateCoordinateDerivative' :
        NormedHasDerivAt
          (fun candidateTime ↦
            matterCoordinateEquiv
              (candidate (canonicalCauchySlicePoint candidateTime space))
              index)
          (fieldDirectionalDerivative
            (fun point ↦ matterCoordinateEquiv (candidate point)) point
              canonicalLorentzianTimeDirection index)
          time := by
      convert candidateCoordinateDerivative using 1 <;>
        simp [projection, Function.comp_def, point]
    have volterraCoordinateDerivative :=
      cauchySafeMatterVolterraOperator_coordinate_timeLine_hasDerivAt
        current initial candidate space time index velocityContinuous
    have curveEq :
        (fun candidateTime ↦
          matterCoordinateEquiv
            (candidate (canonicalCauchySlicePoint candidateTime space))
            index) =
          fun candidateTime ↦
            matterCoordinateEquiv
              (cauchySafeMatterVolterraOperator current initial candidate
                (canonicalCauchySlicePoint candidateTime space)) index := by
      funext candidateTime
      exact congrArg
        (fun value : DiracExteriorMatterCarrier ↦
          matterCoordinateEquiv value index)
        (congrFun fixedPoint
          (canonicalCauchySlicePoint candidateTime space))
    rw [curveEq] at candidateCoordinateDerivative'
    exact candidateCoordinateDerivative'.unique volterraCoordinateDerivative
  have rawDerivativeEq :
      matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point ↦ matterCoordinateEquiv (candidate point)) point
              canonicalLorentzianTimeDirection) =
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          (cauchySafeMatterCandidateActual current candidate) point := by
    have transported :=
      congrArg matterCoordinateEquiv.symm rawDerivativeCoordinatesEq
    simpa [cauchySafeMatterVolterraVelocity] using transported
  have covariantDerivativeEq :
      holonomicMatterCovariantDerivative
          (cauchySafeMatterCandidateActual current candidate) point
          canonicalLorentzianTimeDirection =
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          (cauchySafeMatterCandidateActual current candidate) point := by
    unfold holonomicMatterCovariantDerivative
      cauchySafeMatterCandidateActual
    rw [rawDerivativeEq]
    unfold
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
      holonomicMatterConnectionAction cauchySafeMatterCandidateActual
    abel
  apply
    (cauchySafeMatterDifferentialOperator_eq_zero_iff source current candidate
      point noncharacteristic).2
  exact covariantDerivativeEq

private theorem cauchySafeMatterVolterra_operator_zero_coordinate_timeLine_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (index : MatterCoordinateIndex)
    (candidateDifferentiable :
      DifferentiableAt ℝ
        (fun point ↦ matterCoordinateEquiv (candidate point))
        (canonicalCauchySlicePoint time space))
    (noncharacteristic :
      coframeTemporalPrincipalScalar
        (current.coframe (canonicalCauchySlicePoint time space)) ≠ 0)
    (operatorZero :
      cauchySafeMatterDifferentialOperator source current candidate
        (canonicalCauchySlicePoint time space) = 0) :
    NormedHasDerivAt
      (fun candidateTime ↦
        matterCoordinateEquiv
          (candidate (canonicalCauchySlicePoint candidateTime space)) index)
      (cauchySafeMatterVolterraVelocity current candidate
        (canonicalCauchySlicePoint time space) index)
      time := by
  let point := canonicalCauchySlicePoint time space
  have covariantDerivativeEq :=
    (cauchySafeMatterDifferentialOperator_eq_zero_iff
      source current candidate point noncharacteristic).1 operatorZero
  have rawDerivativeEq :
      matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun point ↦ matterCoordinateEquiv (candidate point)) point
              canonicalLorentzianTimeDirection) =
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          (cauchySafeMatterCandidateActual current candidate) point := by
    unfold cauchySafeMatterCandidateVelocity at covariantDerivativeEq
    simp only [canonicalLorentzianTimeDirection] at covariantDerivativeEq ⊢
    unfold
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    rw [← covariantDerivativeEq]
    unfold holonomicMatterCovariantDerivative holonomicMatterConnectionAction
      cauchySafeMatterCandidateActual
    simp only [canonicalLorentzianTimeDirection]
    abel
  have rawDerivativeCoordinatesEq :
      fieldDirectionalDerivative
          (fun point ↦ matterCoordinateEquiv (candidate point)) point
          canonicalLorentzianTimeDirection =
        cauchySafeMatterVolterraVelocity current candidate point := by
    have transported := congrArg matterCoordinateEquiv rawDerivativeEq
    simpa [cauchySafeMatterVolterraVelocity] using transported
  have candidateTimeDerivative :=
    field_timeLine_hasDerivAt
      (fun point ↦ matterCoordinateEquiv (candidate point)) space time
      candidateDifferentiable
  let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) 2
      (fun _ : MatterCoordinateIndex => ℂ) index).restrictScalars ℝ
  have candidateCoordinateDerivative :=
    projection.hasFDerivAt.comp_hasDerivAt time candidateTimeDerivative
  convert candidateCoordinateDerivative using 1 <;>
    simp [projection, Function.comp_def, point, rawDerivativeCoordinatesEq]

private theorem cauchySafeMatterVolterra_operator_zero_fixedPoint_timeLine
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (initial : StageNineSpatialPoint → DiracExteriorMatterCarrier)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (initialTrace :
      candidate (canonicalCauchySlicePoint 0 space) = initial space)
    (candidateDifferentiable :
      ∀ point, DifferentiableAt ℝ
        (fun candidatePoint ↦ matterCoordinateEquiv (candidate candidatePoint))
        point)
    (velocityContinuous :
      Continuous fun candidateTime ↦
        cauchySafeMatterVolterraVelocity current candidate
          (canonicalCauchySlicePoint candidateTime space))
    (noncharacteristic :
      ∀ point, coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (operatorZero :
      ∀ point,
        cauchySafeMatterDifferentialOperator source current candidate point = 0) :
    candidate (canonicalCauchySlicePoint time space) =
      cauchySafeMatterVolterraOperator current initial candidate
        (canonicalCauchySlicePoint time space) := by
  apply matterCoordinateEquiv.injective
  apply PiLp.ext
  intro index
  let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (PiLp.proj (𝕜 := ℂ) 2
      (fun _ : MatterCoordinateIndex => ℂ) index).restrictScalars ℝ
  have velocityCoordinateContinuous :
      Continuous fun candidateTime ↦
        cauchySafeMatterVolterraVelocity current candidate
          (canonicalCauchySlicePoint candidateTime space) index := by
    have composed := projection.continuous.comp velocityContinuous
    simpa [projection, Function.comp_def] using composed
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := time)
    (fun candidateTime _ ↦
      cauchySafeMatterVolterra_operator_zero_coordinate_timeLine_hasDerivAt
        source current candidate space candidateTime index
        (candidateDifferentiable _)
        (noncharacteristic _)
        (operatorZero _))
    (velocityCoordinateContinuous.intervalIntegrable 0 time)
  have primitiveEq :
      canonicalTimePrimitive
          (cauchySafeMatterVolterraVelocity current candidate)
          (canonicalCauchySlicePoint time space) index =
        matterCoordinateEquiv
            (candidate (canonicalCauchySlicePoint time space)) index -
          matterCoordinateEquiv
            (candidate (canonicalCauchySlicePoint 0 space)) index := by
    have vectorIntegrable :
        IntervalIntegrable
          (fun candidateTime ↦
            cauchySafeMatterVolterraVelocity current candidate
              (canonicalCauchySlicePoint candidateTime space))
          MeasureTheory.volume 0 time :=
      velocityContinuous.intervalIntegrable 0 time
    unfold canonicalTimePrimitive
    simp only [canonicalTimeProjection_slice, canonicalSpatialProjection_slice]
    change projection
        (∫ candidateTime in (0 : ℝ)..time,
          cauchySafeMatterVolterraVelocity current candidate
            (canonicalCauchySlicePoint candidateTime space)) = _
    rw [← projection.intervalIntegral_comp_comm vectorIntegrable]
    simpa [projection, Function.comp_def] using ftc
  have initialCoordinate := congrArg
    (fun value : DiracExteriorMatterCarrier ↦ matterCoordinateEquiv value index)
    initialTrace
  simp only [cauchySafeMatterVolterraOperator,
    canonicalSpatialProjection_slice, map_add,
    LinearEquiv.apply_symm_apply, PiLp.add_apply]
  rw [primitiveEq, ← initialCoordinate]
  abel

private theorem cauchySafeMatterVolterra_operator_zero_fixedPoint
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (initial : StageNineSpatialPoint → DiracExteriorMatterCarrier)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (initialTrace :
      ∀ space,
        candidate (canonicalCauchySlicePoint 0 space) = initial space)
    (candidateDifferentiable :
      ∀ point, DifferentiableAt ℝ
        (fun candidatePoint ↦ matterCoordinateEquiv (candidate candidatePoint))
        point)
    (velocityContinuous :
      ∀ space, Continuous fun candidateTime ↦
        cauchySafeMatterVolterraVelocity current candidate
          (canonicalCauchySlicePoint candidateTime space))
    (noncharacteristic :
      ∀ point, coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (operatorZero :
      ∀ point,
        cauchySafeMatterDifferentialOperator source current candidate point = 0) :
    candidate = cauchySafeMatterVolterraOperator current initial candidate := by
  funext point
  rw [← canonicalCauchySlicePoint_projections point]
  exact cauchySafeMatterVolterra_operator_zero_fixedPoint_timeLine
    source current initial candidate
      (canonicalSpatialProjection point) (canonicalTimeProjection point)
      (initialTrace _) candidateDifferentiable
      (velocityContinuous _) noncharacteristic operatorZero

/-- On a differentiable noncharacteristic candidate, the native Volterra
fixed-point equation is exactly the mother-action zero fiber with its supplied
Cauchy trace. -/
theorem cauchySafeMatterVolterra_fixedPoint_iff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (initial : StageNineSpatialPoint → DiracExteriorMatterCarrier)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (candidateDifferentiable :
      ∀ point, DifferentiableAt ℝ
        (fun candidatePoint ↦ matterCoordinateEquiv (candidate candidatePoint))
        point)
    (velocityContinuous :
      ∀ space, Continuous fun candidateTime ↦
        cauchySafeMatterVolterraVelocity current candidate
          (canonicalCauchySlicePoint candidateTime space))
    (noncharacteristic :
      ∀ point, coframeTemporalPrincipalScalar (current.coframe point) ≠ 0) :
    candidate = cauchySafeMatterVolterraOperator current initial candidate ↔
      (∀ point,
        cauchySafeMatterDifferentialOperator source current candidate point = 0) ∧
      ∀ space,
        candidate (canonicalCauchySlicePoint 0 space) = initial space := by
  constructor
  · intro fixedPoint
    constructor
    · intro point
      rw [← canonicalCauchySlicePoint_projections point]
      exact cauchySafeMatterVolterra_fixedPoint_operator_zero
        source current initial candidate
          (canonicalSpatialProjection point) (canonicalTimeProjection point)
          fixedPoint (candidateDifferentiable _)
          (velocityContinuous _) (noncharacteristic _)
    · intro space
      rw [fixedPoint]
      exact cauchySafeMatterVolterraOperator_zeroSlice
        current initial candidate space
  · rintro ⟨operatorZero, initialTrace⟩
    exact cauchySafeMatterVolterra_operator_zero_fixedPoint
      source current initial candidate initialTrace candidateDifferentiable
      velocityContinuous noncharacteristic operatorZero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterVolterra
