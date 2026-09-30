import H0mework.Physics.DiracEvolution.SafeCanonicalFiniteStep
import H0mework.Physics.GravityTail.FixedCoframeLoadTemporalSpatial01
import H0mework.Physics.DiracEvolution.SafeWeakEnergyRate

/-!
# Fixed P506/L0 canonical affine-boundary Galerkin step

The fixed source has a nonzero constant matter trace.  This module installs
that trace as a source-owned affine lift and generates the zero-boundary
Galerkin correction from the mother-action mass and stiffness operators.  The
constructor reads no residual, target state, or externally supplied Galerkin
family.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep

open DiracExteriorMatterAction
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineP286ActionCauchySplit
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open scoped NNReal

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

private abbrev Input : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

def boundaryLiftCoefficient : DiracMatterGalerkinCoefficient 1 :=
  WithLp.toLp 2 fun index ↦
    matterCoordinateEquiv diracSpinTwoMatterProbe index.2

def boundaryLiftActionResponse
    (input : ℝ × DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  fixedConstantActionResponse input.1 boundaryLiftCoefficient input.2

theorem boundaryLiftActionResponse_joint_continuous :
    Continuous boundaryLiftActionResponse := by
  exact fixedConstantActionResponse_joint_continuous boundaryLiftCoefficient

theorem boundaryLiftActionResponse_continuous (time : ℝ) :
    Continuous (fun space : DiracMatterSpatialCoordinates ↦
      boundaryLiftActionResponse (time, space)) :=
  boundaryLiftActionResponse_joint_continuous.comp
    (continuous_const.prodMk continuous_id)

def boundaryLiftStiffnessFunctional
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount →L[ℝ] ℝ :=
  diracMatterWeakStiffnessInnerCLM
    (fixedP506L0CauchySafeMatterWeakMassMatrix time)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
    (fun _coefficient space ↦ boundaryLiftActionResponse (time, space))
    (diracMatterWeakMassMatrix_spatial_continuous
      fixedP506L0CauchySafeMatterWeakMassMatrix
      fixedP506L0CauchySafeMatterWeakMassMatrix_continuous time)
    (fun mode ↦
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount mode).continuous)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount)
    (fun _coefficient ↦ boundaryLiftActionResponse_continuous time)
    0

theorem boundaryLiftStiffnessFunctional_continuous
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Continuous (boundaryLiftStiffnessFunctional a b testCount) := by
  rw [continuous_clm_apply]
  intro test
  change Continuous fun time ↦
    diracMatterWeakStiffnessFormValue
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun _coefficient space ↦ boundaryLiftActionResponse (time, space))
      test 0
  exact diracMatterWeakStiffnessFormValue_time_continuous
    fixedP506L0CauchySafeMatterWeakMassMatrix
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
    (fun time _coefficient space ↦ boundaryLiftActionResponse (time, space))
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    (fun mode ↦
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount mode).continuous)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount)
    (fun _coefficient ↦ boundaryLiftActionResponse_joint_continuous)
    test 0

def boundaryLiftStiffnessRiesz
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  (InnerProductSpace.toDual ℝ
    (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)).symm
      (boundaryLiftStiffnessFunctional a b testCount time)

theorem boundaryLiftStiffnessRiesz_continuous
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Continuous (boundaryLiftStiffnessRiesz a b testCount) := by
  exact (InnerProductSpace.toDual ℝ
    (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)).symm.continuous.comp
        (boundaryLiftStiffnessFunctional_continuous a b testCount)

def boundaryLiftForcing
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  -(galerkinWeakMassOperator
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
      time).inverse
        (boundaryLiftStiffnessRiesz a b testCount time)

private theorem canonicalMassInverse_continuous
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Continuous fun time ↦
      (galerkinWeakMassOperator
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
        time).inverse := by
  rw [continuous_iff_continuousAt]
  intro time
  have inverseContinuousAt :
      ContinuousAt ContinuousLinearMap.inverse
        (galerkinWeakMassOperator
          (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
          time) :=
    ((fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time).contDiffAt_map_inverse (n := 1)).continuousAt
  exact inverseContinuousAt.comp
    (galerkinWeakMassOperator_continuous
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
      (fixedP506L0CauchySafeMatterWeakMassForm_continuous
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (fun mode ↦
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount mode).continuous)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b testCount))).continuousAt

theorem boundaryLiftForcing_continuous
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Continuous (boundaryLiftForcing a b testCount) := by
  exact ((canonicalMassInverse_continuous a b testCount).clm_apply
    (boundaryLiftStiffnessRiesz_continuous a b testCount)).neg

theorem boundaryLiftForcing_massEquation
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ) :
    galerkinWeakMassOperator
          (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
      time
          (boundaryLiftForcing a b testCount time) +
        boundaryLiftStiffnessRiesz a b testCount time = 0 := by
  have massInvertible :
      (galerkinWeakMassOperator
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
        time).IsInvertible := by
    change
      (galerkinWeakMassOperator
        (fixedP506L0CauchySafeMatterWeakMassForm
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (fun mode ↦
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
              a b testCount mode).continuous)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount)) time).IsInvertible
    exact fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time
  unfold boundaryLiftForcing
  rw [map_neg]
  rw [massInvertible.self_apply_inverse]
  simp

private abbrev BoundaryLiftAffineState
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :=
  ℝ × FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount

private def boundaryLiftAffineOperator
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ) :
    BoundaryLiftAffineState a b testCount →L[ℝ]
      BoundaryLiftAffineState a b testCount :=
  (ContinuousLinearMap.inr ℝ ℝ
      (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)).comp
    ((ContinuousLinearMap.fst ℝ ℝ
          (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
        ).smulRight (boundaryLiftForcing a b testCount time) +
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time).comp
          (ContinuousLinearMap.snd ℝ ℝ
            (FixedP506L0CauchySafeMatterCanonicalCoefficient
              a b testCount)))

@[simp] private theorem boundaryLiftAffineOperator_apply
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (state : BoundaryLiftAffineState a b testCount) :
    boundaryLiftAffineOperator a b testCount time state =
      (0,
        state.1 • boundaryLiftForcing a b testCount time +
          fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time state.2) :=
  rfl

private theorem boundaryLiftAffineOperator_continuous
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Continuous (boundaryLiftAffineOperator a b testCount) := by
  let scalarProjection := ContinuousLinearMap.fst ℝ ℝ
    (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
  have forceLeg : Continuous fun time ↦
      scalarProjection.smulRight (boundaryLiftForcing a b testCount time) :=
    (ContinuousLinearMap.smulRightL ℝ
      (BoundaryLiftAffineState a b testCount)
      (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
      scalarProjection).continuous.comp
        (boundaryLiftForcing_continuous a b testCount)
  have actionLeg : Continuous fun time ↦
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time).comp
          (ContinuousLinearMap.snd ℝ ℝ
            (FixedP506L0CauchySafeMatterCanonicalCoefficient
              a b testCount)) :=
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
      a b testCount).clm_comp continuous_const
  exact continuous_const.clm_comp (forceLeg.add actionLeg)

private theorem exists_boundaryLiftAffineCorrectionCurve_on_Icc
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    ∃ correction : ℝ →
        FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount,
      correction initialTime = 0 ∧
        ∀ time ∈ Set.Icc initialTime timeEnd,
          HasDerivWithinAt correction
            (boundaryLiftForcing a b testCount time +
              fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                a b testCount time (correction time))
            (Set.Icc initialTime timeEnd) time ∧
          galerkinWeakMassOperator
                (fixedP506L0CauchySafeMatterCanonicalWeakMassForm
                  a b testCount)
                time
                (boundaryLiftForcing a b testCount time +
                  fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                    a b testCount time (correction time)) +
              fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
                a b testCount time (correction time) +
              boundaryLiftStiffnessRiesz a b testCount time = 0 := by
  obtain ⟨state, stateInitial, stateEvolution⟩ :=
    exists_galerkinLinearCoefficientCurve_on_Icc
      (boundaryLiftAffineOperator a b testCount)
      (boundaryLiftAffineOperator_continuous a b testCount)
      ((1, 0) : BoundaryLiftAffineState a b testCount)
      initialTime timeEnd timeOrder
  have scalarEq : ∀ time ∈ Set.Icc initialTime timeEnd,
      (state time).1 = 1 := by
    intro time timeMem
    rcases timeOrder.eq_or_lt with timeEq | timeLt
    · subst timeEnd
      have timeOnly : time = initialTime := by
        exact le_antisymm timeMem.2 timeMem.1
      subst time
      exact congrArg Prod.fst stateInitial
    · have scalarDifferentiable : DifferentiableOn ℝ
          (fun candidate ↦ (state candidate).1)
          (Set.Icc initialTime timeEnd) := by
        intro candidate candidateMem
        exact ((stateEvolution candidate candidateMem).hasFDerivWithinAt.fst
          ).differentiableWithinAt
      have scalarDerivative : ∀ candidate ∈ Set.Ico initialTime timeEnd,
          derivWithin (fun target ↦ (state target).1)
            (Set.Icc initialTime timeEnd) candidate = 0 := by
        intro candidate candidateMem
        let projection := ContinuousLinearMap.fst ℝ ℝ
          (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
        have projectionConstant : HasDerivWithinAt
            (fun _target : ℝ ↦ projection) 0
            (Set.Icc initialTime timeEnd) candidate := by
          exact hasDerivWithinAt_const (c := projection) candidate
            (Set.Icc initialTime timeEnd)
        have projected := projectionConstant.clm_apply
          (stateEvolution candidate ⟨candidateMem.1, candidateMem.2.le⟩)
        have projectedZero : HasDerivWithinAt
            (fun target ↦ (state target).1) 0
            (Set.Icc initialTime timeEnd) candidate := by
          simpa [projection, galerkinLinearVelocity] using projected
        exact projectedZero.derivWithin
          ((uniqueDiffOn_Icc timeLt).uniqueDiffWithinAt
            ⟨candidateMem.1, candidateMem.2.le⟩)
      calc
        (state time).1 = (state initialTime).1 :=
          constant_of_derivWithin_zero scalarDifferentiable scalarDerivative
            time timeMem
        _ = 1 := congrArg Prod.fst stateInitial
  refine ⟨fun time ↦ (state time).2, ?_, ?_⟩
  · exact congrArg Prod.snd stateInitial
  · intro time timeMem
    have projected :=
      (stateEvolution time timeMem).hasFDerivWithinAt.snd.hasDerivWithinAt
    refine ⟨?_, ?_⟩
    · simpa [galerkinLinearVelocity, scalarEq time timeMem] using projected
    · have forceEquation := boundaryLiftForcing_massEquation
        a b testCount time
      have massInvertible :
          (galerkinWeakMassOperator
            (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
            time).IsInvertible := by
        change
          (galerkinWeakMassOperator
            (fixedP506L0CauchySafeMatterWeakMassForm
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              (fun mode ↦
                (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                  a b testCount mode).continuous)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
                a b testCount)) time).IsInvertible
        exact fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (fun mode ↦
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
              a b testCount mode).continuous)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
            a b testCount)
          time
      have actionEquation :
          galerkinWeakMassOperator
                (fixedP506L0CauchySafeMatterCanonicalWeakMassForm
                  a b testCount)
                time
                (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                  a b testCount time (state time).2) +
              fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
                a b testCount time (state time).2 = 0 := by
        exact galerkinWeakActionOperator_mass_equation
          (galerkinWeakMassOperator
            (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount))
          (fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
            a b testCount)
          time (state time).2 massInvertible
      rw [map_add]
      calc
        _ =
            (galerkinWeakMassOperator
                (fixedP506L0CauchySafeMatterCanonicalWeakMassForm
                  a b testCount)
                time (boundaryLiftForcing a b testCount time) +
              boundaryLiftStiffnessRiesz a b testCount time) +
            (galerkinWeakMassOperator
                (fixedP506L0CauchySafeMatterCanonicalWeakMassForm
                  a b testCount)
                time
                (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                  a b testCount time (state time).2) +
              fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
                a b testCount time (state time).2) := by abel
        _ = 0 := by rw [forceEquation, actionEquation]; simp

private theorem boundaryLiftAffineCorrectionCurve_eqOn_Icc
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (first second : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (firstInitial : first initialTime = 0)
    (secondInitial : second initialTime = 0)
    (firstEvolution : ∀ time ∈ Set.Icc initialTime timeEnd,
      HasDerivWithinAt first
        (boundaryLiftForcing a b testCount time +
          fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time (first time))
        (Set.Icc initialTime timeEnd) time)
    (secondEvolution : ∀ time ∈ Set.Icc initialTime timeEnd,
      HasDerivWithinAt second
        (boundaryLiftForcing a b testCount time +
          fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time (second time))
        (Set.Icc initialTime timeEnd) time) :
    Set.EqOn first second (Set.Icc initialTime timeEnd) := by
  have differenceEvolution : ∀ time ∈ Set.Icc initialTime timeEnd,
      HasDerivWithinAt (first - second)
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time ((first - second) time))
        (Set.Icc initialTime timeEnd) time := by
    intro time timeMem
    have difference :=
      (firstEvolution time timeMem).sub (secondEvolution time timeMem)
    apply difference.congr_deriv
    rw [Pi.sub_apply, map_sub]
    abel
  have zeroEvolution : ∀ time ∈ Set.Icc initialTime timeEnd,
      HasDerivWithinAt (fun _candidate : ℝ ↦
        (0 : FixedP506L0CauchySafeMatterCanonicalCoefficient
          a b testCount))
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time 0)
        (Set.Icc initialTime timeEnd) time := by
    intro time _timeMem
    simpa using
      (hasDerivWithinAt_const (c :=
        (0 : FixedP506L0CauchySafeMatterCanonicalCoefficient
          a b testCount)) time (Set.Icc initialTime timeEnd))
  have differenceZero := galerkinLinearCoefficientCurve_eqOn_Icc
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
      a b testCount)
    (first - second)
    (fun _candidate : ℝ ↦
      (0 : FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount))
    0 initialTime timeEnd timeOrder
    (by simp [firstInitial, secondInitial]) rfl
    (by simpa [galerkinLinearVelocity] using differenceEvolution)
    (by simpa [galerkinLinearVelocity] using zeroEvolution)
  intro time timeMem
  have zeroRead := differenceZero timeMem
  simpa only [Pi.sub_apply, sub_eq_zero] using zeroRead

def fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    ℝ → FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  Classical.choose
    (exists_boundaryLiftAffineCorrectionCurve_on_Icc
      0 timeEnd timeNonnegative a b testCount)

theorem fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_initial
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount 0 = 0 :=
  (Classical.choose_spec
    (exists_boundaryLiftAffineCorrectionCurve_on_Icc
      0 timeEnd timeNonnegative a b testCount)).1

theorem fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_evolution
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Set.Icc 0 timeEnd) :
    HasDerivWithinAt
      (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
        timeEnd timeNonnegative a b testCount)
      (boundaryLiftForcing a b testCount time +
        fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
            timeEnd timeNonnegative a b testCount time))
      (Set.Icc 0 timeEnd) time :=
  ((Classical.choose_spec
    (exists_boundaryLiftAffineCorrectionCurve_on_Icc
      0 timeEnd timeNonnegative a b testCount)).2 time timeMem).1

theorem fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_operatorEquation
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Set.Icc 0 timeEnd) :
    galerkinWeakMassOperator
          (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
          time
          (boundaryLiftForcing a b testCount time +
            fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b testCount time
              (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
                timeEnd timeNonnegative a b testCount time)) +
        fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
          a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
            timeEnd timeNonnegative a b testCount time) +
        boundaryLiftStiffnessRiesz a b testCount time = 0 :=
  ((Classical.choose_spec
    (exists_boundaryLiftAffineCorrectionCurve_on_Icc
      0 timeEnd timeNonnegative a b testCount)).2 time timeMem).2

theorem fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_eqOn
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (other : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (otherInitial : other 0 = 0)
    (otherEvolution : ∀ time ∈ Set.Icc 0 timeEnd,
      HasDerivWithinAt other
        (boundaryLiftForcing a b testCount time +
          fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time (other time))
        (Set.Icc 0 timeEnd) time) :
    Set.EqOn
      (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
        timeEnd timeNonnegative a b testCount)
      other (Set.Icc 0 timeEnd) := by
  exact boundaryLiftAffineCorrectionCurve_eqOn_Icc
    0 timeEnd timeNonnegative a b testCount _ other
    (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_initial
      timeEnd timeNonnegative a b testCount)
    otherInitial
    (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_evolution
      timeEnd timeNonnegative a b testCount)
    otherEvolution

theorem boundaryLiftStiffnessRiesz_pairing
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    inner ℝ (boundaryLiftStiffnessRiesz a b testCount time) test =
      boundaryLiftStiffnessFunctional a b testCount time test := by
  change
    ((InnerProductSpace.toDual ℝ
      (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount))
        ((InnerProductSpace.toDual ℝ
          (FixedP506L0CauchySafeMatterCanonicalCoefficient
            a b testCount)).symm
          (boundaryLiftStiffnessFunctional a b testCount time))) test = _
  exact congrArg
    (fun functional :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount →L[ℝ] ℝ ↦
        functional test)
    ((InnerProductSpace.toDual ℝ
      (FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
      ).apply_symm_apply
        (boundaryLiftStiffnessFunctional a b testCount time))

theorem fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_weakEquation
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Set.Icc 0 timeEnd)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm
          a b testCount time
          (boundaryLiftForcing a b testCount time +
            fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b testCount time
              (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
                timeEnd timeNonnegative a b testCount time)) test +
        fixedP506L0CauchySafeMatterWeakStiffnessForm
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount)
          time
          (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
            timeEnd timeNonnegative a b testCount time) test +
        boundaryLiftStiffnessFunctional a b testCount time test = 0 := by
  have equation :=
    fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_operatorEquation
      timeEnd timeNonnegative a b testCount time timeMem
  have tested := congrArg (fun value ↦ inner ℝ value test) equation
  rw [inner_add_left, inner_add_left, inner_zero_left,
    real_inner_galerkinWeakMassOperator,
    boundaryLiftStiffnessRiesz_pairing] at tested
  unfold fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator at tested
  rw [fixedP506L0CauchySafeMatterWeakStiffnessOperator_readout] at tested
  simpa only [
    fixedP506L0CauchySafeMatterWeakStiffnessForm,
    diracMatterWeakStiffnessForm_apply] using tested

def fixedP506L0CauchySafeMatterCanonicalAffineMatterField
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : DiracExteriorMatterCarrier :=
  diracSpinTwoMatterProbe +
    diracMatterSpatialGalerkinSynthesis
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
        timeEnd timeNonnegative a b testCount time)
      space

theorem fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_zero
    (space : DiracMatterSpatialCoordinates) :
    fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates 0 space =
      matterCoordinateEquiv diracSpinTwoMatterProbe := by
  unfold fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates
  apply congrArg matterCoordinateEquiv
  change
    fixedP506L0CartanECConstraintCauchySafePreparedActual.matter
        (canonicalCauchySlicePoint 0
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm space)) =
      diracSpinTwoMatterProbe
  rw [fixedP506L0CartanECConstraintCauchySafePreparedActual_fieldInventory.2.2.2.2.2.2.2.1]
  change
    fixedP506L0CartanECConstraintPreparedActual.matter
        (canonicalCauchySlicePoint 0
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm space)) =
      diracSpinTwoMatterProbe
  change
    fixedP506L0CartanECConstraintRestartActual.matter
        (canonicalCauchySlicePoint 0
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm space)) =
      diracSpinTwoMatterProbe
  unfold fixedP506L0CartanECConstraintRestartActual cartanECCauchyTemporalBase
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  exact fixedP506L0ActionSelectedGravityTailBase_matter_zeroSlice_constant _

theorem fixedP506L0CauchySafeMatterCanonicalAffineMatterField_initial
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (space : DiracMatterSpatialCoordinates) :
    matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterCanonicalAffineMatterField
          timeEnd timeNonnegative a b testCount 0 space) =
      fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates 0 space := by
  rw [fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_zero]
  have modeZero
      (mode : Fin
        (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
          a b testCount)) :
      diracMatterGalerkinCoefficientMode
          (0 : FixedP506L0CauchySafeMatterCanonicalCoefficient
            a b testCount) mode = 0 := by
    ext index
    rfl
  simp [fixedP506L0CauchySafeMatterCanonicalAffineMatterField,
    fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_initial,
    diracMatterSpatialGalerkinSynthesis_coordinates, modeZero]

theorem fixedP506L0CauchySafeMatterCanonicalAffineCorrection_zeroOutside
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (outside : ¬ DiracMatterSpatialBoxInterior a b space) :
    diracMatterSpatialGalerkinSynthesis
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
          timeEnd timeNonnegative a b testCount time)
        space = 0 := by
  apply matterCoordinateEquiv.injective
  simp [diracMatterSpatialGalerkinSynthesis_coordinates,
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount _ space outside]

theorem fixedP506L0CauchySafeMatterCanonicalAffineMatterField_eq_lift_onBoundary
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (outside : ¬ DiracMatterSpatialBoxInterior a b space) :
    fixedP506L0CauchySafeMatterCanonicalAffineMatterField
        timeEnd timeNonnegative a b testCount time space =
      diracSpinTwoMatterProbe := by
  rw [fixedP506L0CauchySafeMatterCanonicalAffineMatterField,
    fixedP506L0CauchySafeMatterCanonicalAffineCorrection_zeroOutside
      timeEnd timeNonnegative a b testCount time space outside,
    add_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
