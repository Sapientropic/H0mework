import H0mework.Physics.IdentityGerms.IdentityECCartanRestartOriginFirstGerm

/-!
# Identity-EC Cartan restart origin curvature

The identity-EC Hessian producer installs a quadratic coframe together with
the corresponding affine Levi--Civita first germ.  Re-running the
current-native Cartan producer on that actual recomputes the nonlinear
Levi--Civita connection and the live KIN contorsion from the same action.

This module proves that the two primitive connections have the same value and
the same six canonical internal-pair derivatives at the origin.  Those are
exactly the data read by the literal `dω + ω ∧ ω` curvature.  No curvature
target, equation, residual, phase, branch, or acceptance certificate is an
input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECCartanRestartOriginCurvature

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginFirstGerm
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionVariation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (currentConnection :
      current.gravityConnection = fun point =>
        diracDualFormNativeActionCartanConnectionAt source current point) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment)).gravityConnection 0 =
      (identityECHolonomicCoframeHessianIncrementLocalActualLift
        current increment).gravityConnection 0 := by
  funext formDirection internalOut internalIn
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  rw [identityECHolonomicCoframeHessianIncrementLocalActualLift_connection_origin]
  rw [currentConnection]
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection
  simp only [Pi.add_apply]
  rw [
    diracDualFormNativeActionCartanContorsionAt_identityECHessian_origin]
  rw [currentIdentityCoframe_leviCivita_component_eq_zero
    current currentCoframe 0 formDirection internalOut internalIn]
  have hessianCoframe :=
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_eq_quadratic
      current increment currentCoframe
  rw [hessianCoframe]
  change
    identityECNonlinearLeviCivitaConnection increment 0
        formDirection internalOut internalIn + _ = 0 + _
  rw [identityECNonlinearLeviCivitaConnection_eq_explicitJet]
  have hessianLeviCivitaZero :
      (identityECQuadraticCoframeJet increment 0).lorentzSpinConnection
          formDirection internalOut internalIn = 0 := by
    simpa [identityECQuadraticCoframeJet,
      identityECQuadraticCoframeField, identityECZeroCoframeFirstJet,
      identityECSpinConnectionComponentOfCarrier,
      pointwiseCoframeJetOfCarrier] using
        (identityECZeroCoframeFirstJet_spinConnection_component_eq_zero
          formDirection internalOut internalIn)
  rw [hessianLeviCivitaZero]

/-! ## The six connection derivatives read by curvature -/

private theorem
    lorentzSkewConnectionOfBivectorOneForm_canonicalPair
    (contorsion : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    lorentzSkewConnectionOfBivectorOneForm contorsion formDirection
        (pairFirst internalPair) (pairSecond internalPair) =
      minkowskiInternalSign (pairFirst internalPair) *
        contorsion formDirection internalPair := by
  fin_cases internalPair <;>
    simp [lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.sum_univ_six]

private theorem fieldDirectionalDerivative_add_real_at_origin
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point + second point)
        0 derivativeDirection =
      fieldDirectionalDerivative first 0 derivativeDirection +
        fieldDirectionalDerivative second 0 derivativeDirection := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  rfl

private theorem fieldDirectionalDerivative_const_mul_real_at_origin
    (field : BasePoint → ℝ)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (scalar : ℝ)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => scalar * field point)
        0 derivativeDirection =
      scalar * fieldDirectionalDerivative field 0 derivativeDirection := by
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul fieldDifferentiable scalar]
  rfl

theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connectionDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (currentSmooth : current.Smooth)
    (currentConnection :
      current.gravityConnection = fun point =>
        diracDualFormNativeActionCartanConnectionAt source current point)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    gravityConnectionDerivative
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment))
        0 derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      gravityConnectionDerivative
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment)
        0 derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) := by
  let hessianLeviCivita : BasePoint → ℝ := fun point =>
    (holonomicCoframeFirstJetAt
      (identityECHolonomicCoframeHessianIncrementLocalActualLift
        current increment).coframe point).lorentzSpinConnection
          formDirection (pairFirst internalPair) (pairSecond internalPair)
  let hessianContorsion : BasePoint → ℝ := fun point =>
    diracDualFormNativeActionCartanContorsionAt source
      (identityECHolonomicCoframeHessianIncrementLocalActualLift
        current increment) point formDirection internalPair
  let currentContorsion : BasePoint → ℝ := fun point =>
    diracDualFormNativeActionCartanContorsionAt source current point
      formDirection internalPair
  let affineLeviCivita : BasePoint → ℝ := fun point =>
    identityECLeviCivitaAffineConnectionIncrement increment point
      formDirection (pairFirst internalPair) (pairSecond internalPair)
  let internalSign := minkowskiInternalSign (pairFirst internalPair)
  have restartFunctionEquality :
      (fun point =>
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment)).gravityConnection point formDirection
              (pairFirst internalPair) (pairSecond internalPair)) =
        fun point =>
          hessianLeviCivita point +
            internalSign * hessianContorsion point := by
    funext point
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
    unfold diracDualFormNativeActionCartanConnectionAt
      cartanAffineSpinConnection
    simp only [Pi.add_apply]
    rw [lorentzSkewConnectionOfBivectorOneForm_canonicalPair]
  have hessianPrimitiveFunctionEquality :
      (fun point =>
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment).gravityConnection point formDirection
            (pairFirst internalPair) (pairSecond internalPair)) =
        fun point =>
          internalSign * currentContorsion point + affineLeviCivita point := by
    funext point
    change
      current.gravityConnection point formDirection
            (pairFirst internalPair) (pairSecond internalPair) +
          identityECLeviCivitaAffineConnectionIncrement increment point
            formDirection (pairFirst internalPair)
              (pairSecond internalPair) = _
    rw [currentConnection]
    unfold diracDualFormNativeActionCartanConnectionAt
      cartanAffineSpinConnection
    simp only [Pi.add_apply]
    rw [currentIdentityCoframe_leviCivita_component_eq_zero
      current currentCoframe point formDirection
        (pairFirst internalPair) (pairSecond internalPair)]
    rw [lorentzSkewConnectionOfBivectorOneForm_canonicalPair]
    simp [currentContorsion, affineLeviCivita,
      internalSign]
  have hessianLeviCivitaDifferentiable :
      DifferentiableAt ℝ hessianLeviCivita 0 := by
    exact
      identityECHolonomicCoframeHessianIncrementLocalActualLift_leviCivita_differentiableAt_origin
        current increment currentCoframe formDirection
          (pairFirst internalPair) (pairSecond internalPair)
  rcases
      diracDualFormNativeActionCartanContorsionAt_identityECHessian_differentiableAt
        source current increment currentCoframe currentSmooth formDirection
          internalPair with
    ⟨hessianContorsionDifferentiable,
      currentContorsionDifferentiable⟩
  have scaledHessianContorsionDifferentiable : DifferentiableAt ℝ
      (fun point => internalSign * hessianContorsion point) 0 :=
    (differentiableAt_const (c := internalSign)).mul
      hessianContorsionDifferentiable
  have scaledCurrentContorsionDifferentiable : DifferentiableAt ℝ
      (fun point => internalSign * currentContorsion point) 0 :=
    (differentiableAt_const (c := internalSign)).mul
      currentContorsionDifferentiable
  have affineLeviCivitaDifferentiable :
      DifferentiableAt ℝ affineLeviCivita 0 := by
    exact
      (identityECLeviCivitaAffineConnectionIncrement_smooth increment
        formDirection (pairFirst internalPair) (pairSecond internalPair))
          |>.differentiable (by simp) 0
  have leviCivitaDerivativeEquality :
      fieldDirectionalDerivative hessianLeviCivita 0 derivativeDirection =
        fieldDirectionalDerivative affineLeviCivita 0
          derivativeDirection := by
    exact
      identityECHolonomicCoframeHessianIncrementLocalActualLift_leviCivita_firstGerm
        current increment currentCoframe derivativeDirection formDirection
          internalPair
  have contorsionDerivativeEquality :
      fieldDirectionalDerivative hessianContorsion 0 derivativeDirection =
        fieldDirectionalDerivative currentContorsion 0
          derivativeDirection := by
    have fderivEquality :=
      diracDualFormNativeActionCartanContorsionAt_identityECHessian_fderiv_eq
        source current increment currentCoframe currentSmooth formDirection
          internalPair
    exact congrArg
      (fun derivative : BasePoint →L[ℝ] ℝ =>
        derivative (coordinateDirection derivativeDirection)) fderivEquality
  unfold gravityConnectionDerivative
  change
    fieldDirectionalDerivative
        (fun point =>
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
            (identityECHolonomicCoframeHessianIncrementLocalActualLift
              current increment)).gravityConnection point formDirection
                (pairFirst internalPair) (pairSecond internalPair))
        0 derivativeDirection =
      fieldDirectionalDerivative
        (fun point =>
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment).gravityConnection point formDirection
              (pairFirst internalPair) (pairSecond internalPair))
        0 derivativeDirection
  rw [restartFunctionEquality, hessianPrimitiveFunctionEquality,
    fieldDirectionalDerivative_add_real_at_origin
      hessianLeviCivita (fun point => internalSign * hessianContorsion point)
      hessianLeviCivitaDifferentiable
      scaledHessianContorsionDifferentiable,
    fieldDirectionalDerivative_add_real_at_origin
      (fun point => internalSign * currentContorsion point)
      affineLeviCivita scaledCurrentContorsionDifferentiable
      affineLeviCivitaDifferentiable,
    fieldDirectionalDerivative_const_mul_real_at_origin
      hessianContorsion hessianContorsionDifferentiable,
    fieldDirectionalDerivative_const_mul_real_at_origin
      currentContorsion currentContorsionDifferentiable,
    leviCivitaDerivativeEquality, contorsionDerivativeEquality]
  ring

/-! ## Literal curvature readout -/

/-- Re-running the current-native Cartan producer after the identity-EC
Hessian write preserves the literal origin curvature of that Hessian actual.
The theorem consumes only the source, the already generated current, and its
identity/action-native lineage.  The curvature equality is a producer-
soundness readout, not an independently supplied field equation. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_curvature_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : CoframeHolonomicSecondJet)
    (currentCoframe : current.coframe = fun _ => 1)
    (currentSmooth : current.Smooth)
    (currentConnection :
      current.gravityConnection = fun point =>
        diracDualFormNativeActionCartanConnectionAt source current point) :
    holonomicGravityCurvature
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
          (identityECHolonomicCoframeHessianIncrementLocalActualLift
            current increment)) 0 =
      holonomicGravityCurvature
        (identityECHolonomicCoframeHessianIncrementLocalActualLift
          current increment) 0 := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  rw [
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connectionDerivative_origin
      source current increment currentCoframe currentSmooth
        currentConnection (pairFirst spacetimePair)
          (pairSecond spacetimePair) internalPair,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connectionDerivative_origin
      source current increment currentCoframe currentSmooth
        currentConnection (pairSecond spacetimePair)
          (pairFirst spacetimePair) internalPair]
  have connectionOrigin :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connection_origin
      source current increment currentCoframe currentConnection
  simp_rw [connectionOrigin]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECCartanRestartOriginCurvature
