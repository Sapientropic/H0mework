import H0mework.Physics.DiracEvolution.SafeGalerkinOperator
import H0mework.Physics.DiracEvolution.SafeVolterraLocalRegularity
import H0mework.Physics.SafeCauchy.FixedJointGlobalECJetRegularity
import H0mework.Physics.TimePrimitive.DiagonalHessian

/-!
# Fixed P506/L0 Cauchy-safe Dirac Galerkin evolution

The exact post-EC source/current action write supplies a continuous
finite-dimensional Galerkin operator.  Picard--Lindelöf then generates a local
coefficient curve through arbitrary finite initial data.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveDiagonalHessian
open StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeCauchySafeMatterVolterraLocalRegularity
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
open StageNineDiracMatterGalerkinEvolution
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineRadialCurveIntegralFirstJet
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise NNReal

noncomputable section

set_option autoImplicit false

variable {modeCount : ℕ}

local instance fixedGalerkinP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance fixedGalerkinP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance fixedGalerkinP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

local instance (priority := 10000) fixedGalerkinCoefficientAddCommGroup :
    AddCommGroup (DiracMatterGalerkinCoefficient modeCount) :=
  (PiLp.normedAddCommGroup 2
    (fun _ : Fin modeCount × MatterCoordinateIndex => ℂ)).toAddCommGroup

local instance (priority := 10000) fixedGalerkinCoefficientModule :
    Module ℝ (DiracMatterGalerkinCoefficient modeCount) :=
  (PiLp.normedSpace 2 ℝ
    (fun _ : Fin modeCount × MatterCoordinateIndex => ℂ)).toModule

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev BaseCurrent : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source
    fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev PreEC : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalP286Current Source BaseCurrent

@[irreducible] def fixedP506L0CauchySafeMatterGalerkinInputActual :
    StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalECPathCurrent Source BaseCurrent

/-- The fixed Galerkin input is exactly the EC leg's native action write. -/
theorem fixedP506L0CauchySafeMatterGalerkinInputActual_eq_actionWrite :
    fixedP506L0CauchySafeMatterGalerkinInputActual =
      sourceActionGeneratedDiracDualCauchySafeGlobalECPathWrite
        positiveSmoothUnifiedSource
        (cauchySafeJointGlobalP286Current positiveSmoothUnifiedSource
          (cartanECCauchyTemporalBase positiveSmoothUnifiedSource
            fixedP506L0CartanECConstraintCauchySafePreparedActual)) := by
  unfold fixedP506L0CauchySafeMatterGalerkinInputActual Source BaseCurrent
  rfl

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

/-- The fixed post-EC current driving every canonical finite Galerkin action
is globally smooth in all nine primitive fields. -/
theorem fixedP506L0CauchySafeMatterGalerkinInputActual_smooth :
    fixedP506L0CauchySafeMatterGalerkinInputActual.Smooth := by
  unfold fixedP506L0CauchySafeMatterGalerkinInputActual Source BaseCurrent
  exact
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECPathCurrent_smooth

private abbrev GlobalTemporal : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalTemporalCurrent Source BaseCurrent

private theorem baseCurrent_smooth : BaseCurrent.Smooth :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_smooth
    Source fixedP506L0CartanECConstraintCauchySafePreparedActual
    fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth
    fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate

private theorem baseCurrent_nondegenerate : BaseCurrent.Nondegenerate := by
  intro point
  change Matrix.det
    (fixedP506L0CartanECConstraintCauchySafePreparedActual.coframe point) ≠ 0
  exact fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate point

private theorem baseCurrent_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (BaseCurrent.coframe point) ≠ 0 := by
  change coframeTemporalPrincipalScalar
    (fixedP506L0CartanECConstraintCauchySafePreparedActual.coframe point) ≠ 0
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic point

private theorem current_coframe_contDiff : ContDiff ℝ ∞ Current.coframe := by
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change ContDiff ℝ ∞ BaseCurrent.coframe
  exact holonomicCoframe_contDiff BaseCurrent baseCurrent_smooth

private theorem current_nondegenerate (point : BasePoint) :
    Matrix.det (Current.coframe point) ≠ 0 := by
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change Matrix.det (BaseCurrent.coframe point) ≠ 0
  exact baseCurrent_nondegenerate point

private theorem current_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (Current.coframe point) ≠ 0 := by
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change coframeTemporalPrincipalScalar (BaseCurrent.coframe point) ≠ 0
  exact baseCurrent_noncharacteristic point

private theorem current_gaugeConnection_contDiffAt_zero
    (point : BasePoint)
    (direction : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun target ↦
      p286CoordinateEquiv (Current.gaugeConnection target direction)) point := by
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change ContDiffAt ℝ 0 (fun target ↦
    p286CoordinateEquiv (BaseCurrent.gaugeConnection target direction)) point
  exact (baseCurrent_smooth.2.2.2.2.1 direction).contDiffAt.of_le
    (by norm_num)

private theorem scalarAcceleration_contDiff : ContDiff ℝ ∞
    (completeJointCauchySafeScalarAccelerationProfile Source BaseCurrent) :=
  completeJointCauchySafeScalarAccelerationProfile_contDiff Source BaseCurrent
    baseCurrent_smooth baseCurrent_nondegenerate baseCurrent_noncharacteristic

private theorem globalTemporal_scalar_contDiff :
    ContDiff ℝ 1 GlobalTemporal.scalar := by
  change ContDiff ℝ 1
    (BaseCurrent.scalar + canonicalTimeSecondPrimitive
      (completeJointCauchySafeScalarAccelerationProfile Source BaseCurrent))
  have baseRegular : ContDiff ℝ 1 BaseCurrent.scalar :=
    baseCurrent_smooth.2.2.2.2.2.2.1.of_le (by norm_num)
  have primitiveRegular : ContDiff ℝ 1
      (canonicalTimeSecondPrimitive
        (completeJointCauchySafeScalarAccelerationProfile Source BaseCurrent)) :=
    (canonicalTimeSecondPrimitive_contDiff_two_of_contDiff _
      scalarAcceleration_contDiff).of_le (by norm_num)
  exact baseRegular.add primitiveRegular

private theorem current_scalar_contDiff : ContDiff ℝ 0 Current.scalar := by
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change ContDiff ℝ 0 GlobalTemporal.scalar
  exact globalTemporal_scalar_contDiff.of_le (by norm_num)

private theorem current_gravityConnection_component_contDiff_one
    (direction internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ 1 (fun point ↦
      Current.gravityConnection point direction internalOut internalIn) := by
  have incrementRegular : ContDiff ℝ 1
      (cauchySafeJointGlobalECRadialIncrement Source PreEC) :=
    radialCurveIntegral_contDiff_one_of_contDiff
      (cauchySafeJointGlobalECJetCLM Source PreEC)
      fixedP506L0CartanECConstraintCauchySafeJointGlobalECJetCLM_contDiff_one
  have liftedRegular : ContDiff ℝ 1 (fun point ↦
      radialLorentzConnectionLiftCLM
        (cauchySafeJointGlobalECRadialIncrement Source PreEC point)) :=
    radialLorentzConnectionLiftCLM.contDiff.comp incrementRegular
  have coordinateRegular : ContDiff ℝ 1 (fun point ↦
      radialLorentzConnectionCoordinateCLM direction internalOut internalIn
        (radialLorentzConnectionLiftCLM
          (cauchySafeJointGlobalECRadialIncrement Source PreEC point))) :=
    (radialLorentzConnectionCoordinateCLM direction internalOut internalIn
      ).contDiff.comp liftedRegular
  unfold Current fixedP506L0CauchySafeMatterGalerkinInputActual
  change ContDiff ℝ 1 (fun point ↦
    PreEC.gravityConnection 0 direction internalOut internalIn +
      radialLorentzConnectionCoordinateCLM direction internalOut internalIn
        (radialLorentzConnectionLiftCLM
          (cauchySafeJointGlobalECRadialIncrement Source PreEC point)))
  exact contDiff_const.add coordinateRegular

private theorem synthesis_contDiff_one
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    ContDiff ℝ 1 (fun point ↦ matterCoordinateEquiv
      (cauchySafeMatterGalerkinSynthesis basis coefficient point)) := by
  simp only [cauchySafeMatterGalerkinSynthesis_coordinates]
  exact ContDiff.sum fun mode _ ↦
    (basisRegular mode).smul_const
      (diracMatterGalerkinCoefficientMode coefficient mode)

/-- The exact post-EC action velocity of every finite `C¹` synthesis is
globally continuous. -/
theorem fixedP506L0CauchySafeMatterGalerkinInputActual_volterraVelocity_contDiff_zero
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    ContDiff ℝ 0 (cauchySafeMatterVolterraVelocity Current
      (cauchySafeMatterGalerkinSynthesis basis coefficient)) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact cauchySafeMatterVolterraVelocity_contDiffAt_zero_of_local
    Current (cauchySafeMatterGalerkinSynthesis basis coefficient) point
    (current_nondegenerate point)
    (current_noncharacteristic point)
    (current_coframe_contDiff.contDiffAt.of_le (by norm_num))
    (fun direction internalOut internalIn ↦
      (current_gravityConnection_component_contDiff_one direction internalOut
        internalIn).contDiffAt.of_le (by norm_num))
    current_scalar_contDiff.contDiffAt
    (synthesis_contDiff_one basis basisRegular coefficient).contDiffAt
    (fun direction ↦
      current_gaugeConnection_contDiffAt_zero point direction)

theorem exists_fixedP506L0CauchySafeMatterGalerkinCoefficientCurve
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (sample : Fin modeCount → StageNineSpatialPoint)
    (initial : DiracMatterGalerkinCoefficient modeCount)
    (initialTime : ℝ) :
    ∃ bound : ℝ≥0,
      ∃ coefficient : ℝ → DiracMatterGalerkinCoefficient modeCount,
        coefficient initialTime = initial ∧
          (∀ time ∈
              Set.Icc
                (initialTime - galerkinLinearLocalTimeRadius bound initial)
                (initialTime + galerkinLinearLocalTimeRadius bound initial),
              HasDerivWithinAt coefficient
                (cauchySafeMatterGalerkinAction Current basis sample time
                  (coefficient time))
                (Set.Icc
                  (initialTime - galerkinLinearLocalTimeRadius bound initial)
                  (initialTime + galerkinLinearLocalTimeRadius bound initial))
                time) ∧
            ∀ time ∈
              Set.Icc initialTime
                (initialTime + galerkinLinearLocalTimeRadius bound initial),
              ‖coefficient time‖ ≤
                ‖initial‖ * Real.exp ((bound : ℝ) * (time - initialTime)) := by
  let basisDifferentiable : ∀ mode, Differentiable ℝ (basis mode) :=
    fun mode ↦ (basisRegular mode).differentiable (by norm_num)
  let operator : ℝ →
      DiracMatterGalerkinCoefficient modeCount →L[ℝ]
        DiracMatterGalerkinCoefficient modeCount :=
    cauchySafeMatterGalerkinActionCLM Current basis basisDifferentiable sample
  have operatorContinuous : Continuous operator := by
    rw [continuous_clm_apply]
    intro candidateCoefficient
    change Continuous (fun time ↦
      cauchySafeMatterGalerkinAction Current basis sample time
        candidateCoefficient)
    unfold cauchySafeMatterGalerkinAction
    apply (WithLp.linearEquiv 2 ℂ
      (Fin modeCount × MatterCoordinateIndex → ℂ)).symm.toContinuousLinearEquiv
        |>.continuous.comp
    apply continuous_pi
    intro index
    have full :=
      (fixedP506L0CauchySafeMatterGalerkinInputActual_volterraVelocity_contDiff_zero
        basis basisRegular candidateCoefficient).continuous
    have sliceContinuous : Continuous (fun time ↦
        canonicalCauchySlicePoint time (sample index.1)) := by
      rw [show (fun time ↦ canonicalCauchySlicePoint time (sample index.1)) =
        fun time ↦
          canonicalCauchySlicePoint 0 (sample index.1) +
            time • coordinateDirection canonicalLorentzianTimeDirection by
        funext time
        apply PiLp.ext
        intro direction
        fin_cases direction <;>
          simp [canonicalCauchySlicePoint, coordinateDirection,
            canonicalLorentzianTimeDirection, Fin.sum_univ_three]]
      fun_prop
    have lineContinuous := full.comp sliceContinuous
    let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
      (PiLp.proj (𝕜 := ℂ) 2
        (fun _ : MatterCoordinateIndex => ℂ) index.2).restrictScalars ℝ
    simpa [projection, Function.comp_def] using
      projection.continuous.comp lineContinuous
  obtain ⟨bound, coefficient, initialValue, _, evolution, coefficientBound⟩ :=
    exists_galerkinLinearCoefficientCurve_of_continuous_with_norm_bound operator
      operatorContinuous initial initialTime
  have actionEvolution :
      ∀ time ∈
        Set.Icc
          (initialTime - galerkinLinearLocalTimeRadius bound initial)
          (initialTime + galerkinLinearLocalTimeRadius bound initial),
        HasDerivWithinAt coefficient
          (cauchySafeMatterGalerkinAction Current basis sample time
            (coefficient time))
          (Set.Icc
            (initialTime - galerkinLinearLocalTimeRadius bound initial)
            (initialTime + galerkinLinearLocalTimeRadius bound initial))
          time := by
    intro time timeMem
    simpa [operator, basisDifferentiable, galerkinLinearVelocity,
      fixedGalerkinCoefficientAddCommGroup, fixedGalerkinCoefficientModule] using
      evolution time timeMem
  exact ⟨bound, coefficient, initialValue, actionEvolution, coefficientBound⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
