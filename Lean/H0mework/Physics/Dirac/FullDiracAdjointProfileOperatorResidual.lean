import H0mework.Physics.Dirac.FullDiracAdjointProfileResidual

/-!
# Identity-coframe profile operator residual

The fixed complete-joint profile velocities reduce to one full-carrier
formal-adjoint residual on the same Cartan restart.  No pointwise zero or
P286 restriction is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

namespace SaturationMonoid.PhysicsCore
namespace StageNineFullDiracAdjointProfileOperatorResidual

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506ActionSelectedDiracVectorCurrentTemporalRateZeroSlice
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFullDiracAdjointMaterial
open StageNineFullDiracAdjointCoupledTemporalResidual
open StageNineFullDiracAdjointProfileResidual
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286DiracAdjointCoefficientMaterial
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift

noncomputable section

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

/-- Public dependent readout of the exact restart current already used by
the profile operator residual.  It exposes no constructor or new source. -/
def profileOperatorRestartAt
    (point : BasePoint) : StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent Source Carry point

private abbrev Primal (point : BasePoint) : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (profileOperatorRestartAt point)

private abbrev Profiles (point : BasePoint) : CompleteJointGeneratedProfiles :=
  sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry point

/-- The fixed Carry has the identity coframe first jet at every point. -/
theorem carry_coframeFirstJet_identity (point : BasePoint) :
    holonomicCoframeFirstJetAt Carry.coframe point =
      identityCoframeMatterGeometry := by
  rw [actionSelectedCarry_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

/-- Recentring and the Cartan restart preserve that same complete first
jet. -/
theorem restart_coframeFirstJet_identity (point : BasePoint) :
    holonomicCoframeFirstJetAt (profileOperatorRestartAt point).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold profileOperatorRestartAt completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_coframeFirstJet_origin]
  exact carry_coframeFirstJet_identity point

/-- The primal response write leaves the restart coframe unchanged. -/
theorem primal_coframeFirstJet_identity (point : BasePoint) :
    holonomicCoframeFirstJetAt (Primal point).coframe 0 =
      identityCoframeMatterGeometry := by
  unfold Primal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe]
  exact restart_coframeFirstJet_identity point

/-- Full dual-valued mismatch between the two source-generated response
operators. -/
def profileResponseFormalAdjointResidual
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
      (Primal point) 0 -
    fullCanonicalDiracAdjoint
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (profileOperatorRestartAt point) 0)

/-- The finite profile residual is the faithful coordinate read of the full
response residual. -/
theorem profileVelocityFormalAdjointResidual_eq_responseCoordinates
    (point : BasePoint) :
    profileVelocityFormalAdjointResidual point =
      matterDualCoordinates (profileResponseFormalAdjointResidual point) := by
  unfold StageNineFullDiracAdjointProfileResidual.profileVelocityFormalAdjointResidual
    fullCanonicalDiracAdjointCoordinate profileResponseFormalAdjointResidual
    Primal profileOperatorRestartAt
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity,
    matterCoordinateEquiv.symm_apply_apply, matterDualCoordinates_sub]

/-- Identity-first-jet reduction of the live adjoint response. -/
theorem profileResponseFormalAdjointResidual_eq_identityResponse
    (point : BasePoint) :
    profileResponseFormalAdjointResidual point =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          (Primal point) 0 -
        fullCanonicalDiracAdjoint
          (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
            (profileOperatorRestartAt point) 0) := by
  unfold profileResponseFormalAdjointResidual
  rw [holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
    _ _ (primal_coframeFirstJet_identity point)]

/-- The primal writer changes none of the point data read by the adjoint
response. -/
theorem primal_identityActionVelocity_eq_restart (point : BasePoint) :
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
        (Primal point) 0 =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
        (profileOperatorRestartAt point) 0 := by
  apply
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity_eq_of_pointData
  · rfl
  · rfl
  · rfl
  · rfl
  · intro direction
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rfl

/-- Both response operators now live on the same exact Cartan restart. -/
theorem profileResponseFormalAdjointResidual_eq_restartIdentityResponse
    (point : BasePoint) :
    profileResponseFormalAdjointResidual point =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          (profileOperatorRestartAt point) 0 -
        fullCanonicalDiracAdjoint
          (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
            (profileOperatorRestartAt point) 0) := by
  rw [profileResponseFormalAdjointResidual_eq_identityResponse,
    primal_identityActionVelocity_eq_restart]

/-- First uneliminated full-carrier term after the source, recentering,
Cartan and identity-coframe readouts have been consumed. -/
def identityCoframeProfileOperatorResidual
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
      (profileOperatorRestartAt point) 0).comp
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) -
    fullCanonicalDiracAdjoint
      (-identityCoframeMatterTimePrincipal
          (holonomicDiracDualCurrentCoframeMatterKnownVector
            (profileOperatorRestartAt point) 0) -
        holonomicMatterConnectionAction (profileOperatorRestartAt point) 0
          canonicalLorentzianTimeDirection)

/-- The response residual is definitionally the identity-coframe operator
residual. -/
theorem profileResponseFormalAdjointResidual_eq_operatorResidual
    (point : BasePoint) :
    profileResponseFormalAdjointResidual point =
      identityCoframeProfileOperatorResidual point := by
  rw [profileResponseFormalAdjointResidual_eq_restartIdentityResponse]
  unfold identityCoframeProfileOperatorResidual
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    actionGeneratedCurrentCoframeMatterTemporalDerivative
  have coframeOne : (profileOperatorRestartAt point).coframe 0 = 1 :=
    coframe_eq_one_of_identity_firstJet _ _
      (restart_coframeFirstJet_identity point)
  rw [coframeOne, currentCoframeMatterTemporalPrincipalInverse_one]

/-- Exact finite-coordinate operator residual. -/
theorem profileVelocityFormalAdjointResidual_eq_operatorCoordinates
    (point : BasePoint) :
    profileVelocityFormalAdjointResidual point =
      matterDualCoordinates (identityCoframeProfileOperatorResidual point) := by
  rw [profileVelocityFormalAdjointResidual_eq_responseCoordinates,
    profileResponseFormalAdjointResidual_eq_operatorResidual]

/-- The runtime source residual is the canonical-time primitive of the exact
full-carrier operator residual. -/
theorem coupledTemporalSourceOperatorResidual_eq_operatorPrimitive
    (point : BasePoint) :
    coupledTemporalSourceOperatorResidual point =
      matterDualOfCoordinates
        (canonicalTimePrimitive
          (fun candidate =>
            matterDualCoordinates
              (identityCoframeProfileOperatorResidual candidate)) point) := by
  rw [coupledTemporalSourceOperatorResidual_eq_profileVelocityPrimitive]
  apply congrArg matterDualOfCoordinates
  apply congrArg (fun profile : BasePoint → MatterCoordinateCarrier =>
    canonicalTimePrimitive profile point)
  funext candidate
  exact profileVelocityFormalAdjointResidual_eq_operatorCoordinates candidate

/-! ## Exact formal-adjoint action law -/

/-- Equality of the two response operators generated at the same restart. -/
def ProfileVelocityFormalAdjointAt (point : BasePoint) : Prop :=
  holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
      (Primal point) 0 =
    fullCanonicalDiracAdjoint
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (profileOperatorRestartAt point) 0)

theorem profileVelocityFormalAdjointResidual_zero_iff_operator
    (point : BasePoint) :
    profileVelocityFormalAdjointResidual point = 0 ↔
      ProfileVelocityFormalAdjointAt point := by
  unfold profileVelocityFormalAdjointResidual
    ProfileVelocityFormalAdjointAt
    fullCanonicalDiracAdjointCoordinate
  rw [sub_eq_zero]
  simp only [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity,
    sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    matterCoordinateEquiv.symm_apply_apply]
  constructor
  · exact fun equality => matterDualCoordinates_injective equality
  · intro equality
    exact congrArg matterDualCoordinates equality

private theorem restart_coframe_origin (point : BasePoint) :
    (profileOperatorRestartAt point).coframe 0 = 1 :=
  coframe_eq_one_of_identity_firstJet _ _
    (restart_coframeFirstJet_identity point)

private theorem restart_nondegenerate_origin (point : BasePoint) :
    Matrix.det ((profileOperatorRestartAt point).coframe 0) ≠ 0 := by
  rw [restart_coframe_origin]
  norm_num

private theorem restart_noncharacteristic_origin (point : BasePoint) :
    coframeTemporalPrincipalScalar
      ((profileOperatorRestartAt point).coframe 0) ≠ 0 := by
  rw [restart_coframe_origin, coframeTemporalPrincipalScalar_one]
  norm_num

private theorem primal_conjugateMatter_eq_restart (point : BasePoint) :
    (Primal point).conjugateMatter =
      (profileOperatorRestartAt point).conjugateMatter := by
  unfold Primal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    installMatterLinearTimeResponse_conjugateMatter]

private theorem primal_conjugateMatterDerivative_eq_restart
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual (Primal point) 0 direction =
      holonomicConjugateMatterDerivativeDual
        (profileOperatorRestartAt point) 0 direction := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [primal_conjugateMatter_eq_restart]

private theorem profile_adjointVelocity_eq_restartActionVelocity
    (point : BasePoint) :
    (Profiles point).adjointVelocity =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (profileOperatorRestartAt point) 0 := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
  apply
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro direction
    exact primal_conjugateMatterDerivative_eq_restart point direction

/-- Earliest unpaid positive law: the canonical adjoint of the raw primal
response must solve the independently generated adjoint action equation on
the same restart current. -/
def CanonicalRawVelocitySatisfiesAdjointActionAt
    (point : BasePoint) : Prop :=
  HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
    (profileOperatorRestartAt point) 0
    (fullCanonicalDiracAdjoint
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (profileOperatorRestartAt point) 0))

/-- Action-law uniqueness removes the selected adjoint velocity from the
remaining seam. -/
theorem profileVelocityFormalAdjoint_operator_iff_canonicalActionLaw
    (point : BasePoint) :
    ProfileVelocityFormalAdjointAt point ↔
      CanonicalRawVelocitySatisfiesAdjointActionAt point := by
  have velocityEq :
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (Primal point) 0 =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (profileOperatorRestartAt point) 0 := by
    unfold Primal profileOperatorRestartAt
    rw [← sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
    exact profile_adjointVelocity_eq_restartActionVelocity point
  have generatedLaw :
      HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
        (profileOperatorRestartAt point) 0
        (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (profileOperatorRestartAt point) 0) :=
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
      (profileOperatorRestartAt point) 0 (restart_nondegenerate_origin point)
      (restart_noncharacteristic_origin point)
  constructor
  · intro operatorEquality
    unfold ProfileVelocityFormalAdjointAt at operatorEquality
    unfold CanonicalRawVelocitySatisfiesAdjointActionAt
    rw [velocityEq] at operatorEquality
    exact operatorEquality ▸ generatedLaw
  · intro canonicalLaw
    unfold CanonicalRawVelocitySatisfiesAdjointActionAt at canonicalLaw
    unfold ProfileVelocityFormalAdjointAt
    rw [velocityEq]
    exact
      holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_unique
        (profileOperatorRestartAt point) 0
        (restart_nondegenerate_origin point)
        (restart_noncharacteristic_origin point) _ _ generatedLaw canonicalLaw

theorem profileVelocityFormalAdjointResidual_zero_iff_canonicalActionLaw
    (point : BasePoint) :
    profileVelocityFormalAdjointResidual point = 0 ↔
      CanonicalRawVelocitySatisfiesAdjointActionAt point := by
  rw [profileVelocityFormalAdjointResidual_zero_iff_operator,
    profileVelocityFormalAdjoint_operator_iff_canonicalActionLaw]

/-- Identity-coframe expansion of the missing source action law. -/
def CanonicalRawVelocityRightChiralBalanceAt
    (point : BasePoint) : Prop :=
  HolonomicDiracDualRightChiralIdentityCoframeConjugateMatterTimeActionLaw
    (profileOperatorRestartAt point) 0
    (fullCanonicalDiracAdjoint
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (profileOperatorRestartAt point) 0))

theorem canonicalRawVelocity_actionLaw_iff_rightChiralBalance
    (point : BasePoint) :
    CanonicalRawVelocitySatisfiesAdjointActionAt point ↔
      CanonicalRawVelocityRightChiralBalanceAt point := by
  unfold CanonicalRawVelocitySatisfiesAdjointActionAt
    CanonicalRawVelocityRightChiralBalanceAt
  exact
    holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff_rightChiralIdentity_of_firstJet
      (profileOperatorRestartAt point) 0 _
        (restart_coframeFirstJet_identity point)

theorem profileVelocityFormalAdjointResidual_zero_iff_rightChiralBalance
    (point : BasePoint) :
    profileVelocityFormalAdjointResidual point = 0 ↔
      CanonicalRawVelocityRightChiralBalanceAt point := by
  rw [profileVelocityFormalAdjointResidual_zero_iff_canonicalActionLaw,
    canonicalRawVelocity_actionLaw_iff_rightChiralBalance]

/-! ## Nontrivial normalization check on the generated time axis -/

private def timeAxisMatterVelocityCoefficient (time : ℝ) : Fin 4 → ℂ :=
  fun spinIndex =>
    if spinIndex = 3 then
      Complex.I * ((5 / 9 : ℝ) * c3h181StrongCouplingSquared * time)
    else if spinIndex = 2 then
      Complex.I * ((5 / 6 : ℝ) *
        c3h181StrongCouplingSquared * time ^ 2)
    else 0

private theorem timeAxis_profileMatterVelocity_material
    (time : ℝ) :
    (Profiles (canonicalCauchySlicePoint time
      (0 : StageNineSpatialPoint))).matterVelocity =
      p286SpinMatter (timeAxisMatterVelocityCoefficient time) := by
  rw [fixedActionSelectedTimeAxisMatterVelocity_normalForm]
  funext spinIndex
  simp [timeAxisMatterVelocityCoefficient, p286SpinMatter]

private theorem timeAxis_profileAdjointVelocity_material
    (time : ℝ) :
    (Profiles (canonicalCauchySlicePoint time
      (0 : StageNineSpatialPoint))).adjointVelocity =
      p286SpinAdjoint (timeAxisMatterVelocityCoefficient time) := by
  apply LinearMap.ext
  intro matter
  rw [fixedActionSelectedTimeAxisAdjointVelocity_apply_normalForm]
  simp [timeAxisMatterVelocityCoefficient, p286SpinAdjoint,
    p286SpinCoordinate]
  simp only [starRingEnd_apply, star_ofNat]
  ring

/-- The open operator law closes on the whole nontrivial time axis, so the
remaining term is genuinely transverse rather than a normalization seam. -/
theorem profileVelocityFormalAdjointResidual_timeAxis_zero
    (time : ℝ) :
    profileVelocityFormalAdjointResidual
      (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) = 0 := by
  unfold profileVelocityFormalAdjointResidual
    fullCanonicalDiracAdjointCoordinate
  rw [timeAxis_profileMatterVelocity_material,
    timeAxis_profileAdjointVelocity_material,
    matterCoordinateEquiv.symm_apply_apply,
    fullCanonicalDiracAdjoint_p286SpinMatter]
  simp

end
end StageNineFullDiracAdjointProfileOperatorResidual
end SaturationMonoid.PhysicsCore
