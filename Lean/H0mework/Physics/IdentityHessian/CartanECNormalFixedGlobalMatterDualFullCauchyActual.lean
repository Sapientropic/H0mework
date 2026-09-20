import H0mework.Physics.Coframe.CurrentCoframeMatterTimeResponseActualLift
import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalFullCauchyActual
import H0mework.Physics.Holonomic.HolonomicIdentityCoframeConjugateMatterActionAcceptance
import H0mework.Physics.Coframe.IdentityCoframeConjugateMatterTimeResponseActualLift

/-!
# Fixed P506/L0 matter-dual/full-EC critical-pair successor

The fixed global KIN-16 actual already has one complete Einstein--Cartan
Cauchy write.  Its Cartan connection differs from the earlier matter germ,
so an old matter receipt cannot be transported across that write.  This
module instead lets the current action generate fresh primal and adjoint
temporal responses, then recomputes the complete EC write from the resulting
same actual:

```text
fixed P506/L0 KIN-16 full-Cauchy actual
  -> current-coframe primal Dirac write
  -> current-owned adjoint Dirac write
  -> live twelve-plus-four EC write
  -> one matter-dual/full-EC successor.
```

Every constructor consumes only a previously generated actual (and, for the
EC leg, the proof-free source).  No residual, target jet, response value,
branch, coefficient, equation, or stationarity receipt is accepted.  The
equation readbacks are producer-soundness for these action writes, while the
same-output conjunction is the synchronization checkpoint.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000

/-! ## Current-owned critical-pair producer -/

/-- Recompute the unique primal temporal Dirac response from the complete
KIN-16/EC current. -/
def fixedGlobalPrimalMatterWrittenActual :
    StageNineHolonomicConfiguration :=
  actionGeneratedCurrentCoframeMatterTimeResponseActual
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual

/-- Recompute the unique adjoint temporal response after the primal write.
This changes no primal or gravitational field. -/
def fixedGlobalMatterDualWrittenActual :
    StageNineHolonomicConfiguration :=
  actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
    fixedGlobalPrimalMatterWrittenActual

/-- Recompute the live full EC response after both matter writes.  This is
the synchronized successor judged below. -/
def positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    positiveSmoothUnifiedSource fixedGlobalMatterDualWrittenActual

/-! ## Primitive-field and regularity seams -/

@[simp] theorem fixedGlobalPrimalMatterWrittenActual_coframe :
    fixedGlobalPrimalMatterWrittenActual.coframe =
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe :=
  rfl

@[simp] theorem fixedGlobalMatterDualWrittenActual_coframe :
    fixedGlobalMatterDualWrittenActual.coframe =
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe :=
  rfl

@[simp] theorem fixedGlobalMatterDualFullCauchy_coframe :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe =
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe := by
  rw [positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    fixedGlobalMatterDualWrittenActual_coframe]

theorem fixedGlobalPrimalMatterWrittenActual_smooth :
    fixedGlobalPrimalMatterWrittenActual.Smooth :=
  actionGeneratedCurrentCoframeMatterTimeResponseActual_smooth _
    fixedGlobalFullCauchy_smooth

theorem fixedGlobalMatterDualWrittenActual_smooth :
    fixedGlobalMatterDualWrittenActual.Smooth :=
  actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_smooth _
    fixedGlobalPrimalMatterWrittenActual_smooth

theorem fixedGlobalMatterDualFullCauchy_smooth :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.Smooth :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_smooth _ _
    fixedGlobalMatterDualWrittenActual_smooth

theorem fixedGlobalMatterDualFullCauchy_coframe_origin :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe
        0 =
      1 := by
  rw [fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe_origin]

theorem fixedGlobalMatterDualFullCauchy_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe
        0 =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  have zeroSlice :=
    fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice 0
  have contactZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  simpa [contactZero] using zeroSlice

private theorem fixedGlobalFullCauchy_noncharacteristic :
    coframeTemporalPrincipalScalar
        (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.coframe
          0) ≠
      0 := by
  rw [fixedGlobalFullCauchy_coframe_origin]
  simp

/-! ## Primal matter action and acceptance -/

/-- At chart/contact zero the current-coframe temporal action law is exactly
the primitive Dirac--Yukawa equation.  This is a downstream algebraic
readout; it constructs no response. -/
theorem generatedContinuumMatterVector_zero_of_currentCoframeActionLaw
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (actionLaw :
      HolonomicCurrentCoframeMatterTimeActionLaw configuration 0
        (holonomicMatterCovariantDerivative configuration 0
          canonicalLorentzianTimeDirection)) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField configuration 0) =
      0 := by
  unfold generatedContinuumMatterVector
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart]
  unfold HolonomicCurrentCoframeMatterTimeActionLaw at actionLaw
  unfold CurrentCoframeMatterTemporalActionLaw at actionLaw
  unfold currentCoframeMatterTemporalPrincipal at actionLaw
  unfold holonomicCurrentCoframeMatterKnownVector at actionLaw
  simpa [canonicalLorentzianTimeDirection, Fin.sum_univ_four,
    Fin.sum_univ_three, add_assoc] using actionLaw

/-- At the canonical chart/contact, the primitive Dirac--Yukawa equation
also reads back as the current-coframe temporal action law.  This is the
reverse direction of
`generatedContinuumMatterVector_zero_of_currentCoframeActionLaw`; neither
direction constructs a matter response. -/
theorem currentCoframeActionLaw_of_generatedContinuumMatterVector_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (vectorZero :
      generatedContinuumMatterVector source 0 0
          (toContinuumPointField configuration 0) =
        0) :
    HolonomicCurrentCoframeMatterTimeActionLaw configuration 0
      (holonomicMatterCovariantDerivative configuration 0
        canonicalLorentzianTimeDirection) := by
  unfold generatedContinuumMatterVector at vectorZero
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart] at vectorZero
  unfold HolonomicCurrentCoframeMatterTimeActionLaw
    CurrentCoframeMatterTemporalActionLaw
    currentCoframeMatterTemporalPrincipal
    holonomicCurrentCoframeMatterKnownVector
  simpa [canonicalLorentzianTimeDirection, Fin.sum_univ_four,
    Fin.sum_univ_three, add_assoc] using vectorZero

theorem fixedGlobalPrimalMatterWrittenActual_actionLaw :
    HolonomicCurrentCoframeMatterTimeActionLaw
      fixedGlobalPrimalMatterWrittenActual 0
      (holonomicMatterCovariantDerivative
        fixedGlobalPrimalMatterWrittenActual 0
        canonicalLorentzianTimeDirection) :=
  actionGeneratedCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw
    _ fixedGlobalFullCauchy_smooth
    fixedGlobalFullCauchy_noncharacteristic

theorem fixedGlobalPrimalMatterWrittenActual_diracYukawa :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField fixedGlobalPrimalMatterWrittenActual 0) =
      0 :=
  generatedContinuumMatterVector_zero_of_currentCoframeActionLaw
    positiveSmoothUnifiedSource fixedGlobalPrimalMatterWrittenActual
    fixedGlobalPrimalMatterWrittenActual_actionLaw

/-! ## Same-output action-law transport -/

@[simp] theorem fixedGlobalMatterDualFullCauchy_matter :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.matter =
      fixedGlobalPrimalMatterWrittenActual.matter :=
  rfl

@[simp] theorem fixedGlobalMatterDualFullCauchy_conjugateMatter :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.conjugateMatter =
      fixedGlobalMatterDualWrittenActual.conjugateMatter :=
  rfl

@[simp] theorem fixedGlobalMatterDualFullCauchy_gaugeConnection :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.gaugeConnection =
      fixedGlobalPrimalMatterWrittenActual.gaugeConnection :=
  rfl

@[simp] theorem fixedGlobalMatterDualFullCauchy_scalar :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.scalar =
      fixedGlobalPrimalMatterWrittenActual.scalar :=
  rfl

theorem fixedGlobalMatterDualFullCauchy_gravityConnection_origin :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.gravityConnection
        0 =
      fixedGlobalPrimalMatterWrittenActual.gravityConnection 0 := by
  calc
    _ = fixedGlobalMatterDualWrittenActual.gravityConnection 0 :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero
        _ _
    _ = fixedGlobalPrimalMatterWrittenActual.gravityConnection 0 := rfl

private theorem fixedGlobalMatterDualFullCauchy_matterCovariantDerivative
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0 direction =
      holonomicMatterCovariantDerivative
        fixedGlobalPrimalMatterWrittenActual 0 direction := by
  unfold holonomicMatterCovariantDerivative
  rw [fixedGlobalMatterDualFullCauchy_matter,
    fixedGlobalMatterDualFullCauchy_gravityConnection_origin,
    fixedGlobalMatterDualFullCauchy_gaugeConnection]

/-- The final live EC write preserves the freshly generated primal
Dirac--Yukawa equation at the common contact. -/
theorem fixedGlobalMatterDualFullCauchy_diracYukawa :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
          0) =
      0 := by
  have primal := fixedGlobalPrimalMatterWrittenActual_diracYukawa
  unfold generatedContinuumMatterVector at primal ⊢
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart] at primal ⊢
  rw [fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalMatterDualFullCauchy_scalar,
    fixedGlobalMatterDualFullCauchy_matter]
  simp_rw [fixedGlobalMatterDualFullCauchy_matterCovariantDerivative]
  exact primal

theorem fixedGlobalMatterDualWrittenActual_adjointActionLaw :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      fixedGlobalMatterDualWrittenActual 0
      (holonomicConjugateMatterDerivativeDual
        fixedGlobalMatterDualWrittenActual 0
        canonicalLorentzianTimeDirection) :=
  actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw
    _ fixedGlobalPrimalMatterWrittenActual_smooth

private theorem fixedGlobalMatterDualFullCauchy_conjugateDerivativeDual
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0 direction =
      holonomicConjugateMatterDerivativeDual
        fixedGlobalMatterDualWrittenActual 0 direction := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [fixedGlobalMatterDualFullCauchy_conjugateMatter]

private theorem fixedGlobalMatterDualFullCauchy_gaugeConnection_dual :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.gaugeConnection =
      fixedGlobalMatterDualWrittenActual.gaugeConnection := by
  calc
    _ = fixedGlobalPrimalMatterWrittenActual.gaugeConnection :=
      fixedGlobalMatterDualFullCauchy_gaugeConnection
    _ = fixedGlobalMatterDualWrittenActual.gaugeConnection := rfl

private theorem fixedGlobalMatterDualFullCauchy_scalar_dual :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.scalar =
      fixedGlobalMatterDualWrittenActual.scalar := by
  calc
    _ = fixedGlobalPrimalMatterWrittenActual.scalar :=
      fixedGlobalMatterDualFullCauchy_scalar
    _ = fixedGlobalMatterDualWrittenActual.scalar := rfl

private theorem
    fixedGlobalMatterDualFullCauchy_adjointConnectionOperator :
    holonomicIdentityCoframeMatterConnectionOperator
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0 =
      holonomicIdentityCoframeMatterConnectionOperator
        fixedGlobalMatterDualWrittenActual 0 := by
  funext direction
  unfold holonomicIdentityCoframeMatterConnectionOperator
  rw [fixedGlobalMatterDualFullCauchy_gravityConnection_origin,
    fixedGlobalMatterDualFullCauchy_gaugeConnection_dual]
  rfl

private theorem
    fixedGlobalMatterDualFullCauchy_adjointAlgebraicOperator :
    holonomicIdentityCoframeMatterAlgebraicOperator
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0 =
      holonomicIdentityCoframeMatterAlgebraicOperator
        fixedGlobalMatterDualWrittenActual 0 := by
  unfold holonomicIdentityCoframeMatterAlgebraicOperator
  rw [fixedGlobalMatterDualFullCauchy_adjointConnectionOperator,
    fixedGlobalMatterDualFullCauchy_scalar_dual]

private theorem
    fixedGlobalMatterDualFullCauchy_adjointSpatialTransport :
    holonomicIdentityCoframeConjugateMatterSpatialTransport
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0 =
      holonomicIdentityCoframeConjugateMatterSpatialTransport
        fixedGlobalMatterDualWrittenActual 0 := by
  unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
  simp_rw [fixedGlobalMatterDualFullCauchy_conjugateDerivativeDual]

/-- The adjoint temporal action law is re-read on the final EC successor,
not retained as an opaque pre-write receipt. -/
theorem fixedGlobalMatterDualFullCauchy_adjointActionLaw :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
      0
      (holonomicConjugateMatterDerivativeDual
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0 canonicalLorentzianTimeDirection) := by
  have law := fixedGlobalMatterDualWrittenActual_adjointActionLaw
  unfold HolonomicIdentityCoframeConjugateMatterTimeActionLaw at law ⊢
  rw [fixedGlobalMatterDualFullCauchy_conjugateDerivativeDual,
    fixedGlobalMatterDualFullCauchy_adjointSpatialTransport,
    fixedGlobalMatterDualFullCauchy_conjugateMatter,
    fixedGlobalMatterDualFullCauchy_adjointAlgebraicOperator]
  exact law

theorem fixedGlobalMatterDualFullCauchy_adjointTimeDerivative_unique
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier)
    (candidateLaw :
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0 candidate) :
    candidate =
      holonomicConjugateMatterDerivativeDual
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0 canonicalLorentzianTimeDirection :=
  holonomicIdentityCoframeConjugateMatterTimeActionLaw_unique _ _ _ _
    candidateLaw fixedGlobalMatterDualFullCauchy_adjointActionLaw

/-! ## Live EC and Cartan closure on the same successor -/

theorem fixedGlobalMatterDualFullCauchy_simplicity :
    FormNativeGravitySimplicityEquation
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity _ _

theorem fixedGlobalMatterDualFullCauchy_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
    _ _

theorem fixedGlobalMatterDualFullCauchy_simultaneousECBalance :
    (identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
            0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual) =
      0) ∧
    (identityDiracDualECConstraintObservation
          (holonomicGravityCurvature
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
            0) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual) =
      0) :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simultaneousBalance
    _ _

theorem fixedGlobalMatterDualFullCauchy_EC_covector_zero :
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
            0) +
        diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
          positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual =
      0 := by
  rcases fixedGlobalMatterDualFullCauchy_simultaneousECBalance with
    ⟨evolution, constraint⟩
  apply (coframeCovector_eq_iff_coordinateDirections _ _).2
  intro row column
  fin_cases column
  · have coordinate := congrFun constraint row
    simpa [identityDiracDualECConstraintObservation,
      identityECConstraintCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 0
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 1
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 2
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate

private theorem
    fixedGlobalMatterDualFullCauchy_gravityConnection_origin_eq_previous :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.gravityConnection
        0 =
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.gravityConnection
        0 := by
  calc
    _ = fixedGlobalPrimalMatterWrittenActual.gravityConnection 0 :=
      fixedGlobalMatterDualFullCauchy_gravityConnection_origin
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.gravityConnection
          0 := rfl

private theorem
    fixedGlobalMatterDualFullCauchy_matter_origin_eq_previous :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.matter
        0 =
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.matter
        0 := by
  rw [fixedGlobalMatterDualFullCauchy_matter]
  exact actionGeneratedCurrentCoframeMatterTimeResponseActual_matter_origin _

private theorem
    fixedGlobalMatterDualFullCauchy_conjugate_origin_eq_previous :
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.conjugateMatter
        0 =
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.conjugateMatter
        0 := by
  rw [fixedGlobalMatterDualFullCauchy_conjugateMatter]
  calc
    fixedGlobalMatterDualWrittenActual.conjugateMatter 0 =
        fixedGlobalPrimalMatterWrittenActual.conjugateMatter 0 :=
      actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin
        _
    _ =
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual.conjugateMatter
          0 := rfl

/-- Both matter writes preserve the Cartan source values at the contact, and
the final EC write preserves their coframe and connection contact.  The
torsion--spin equation is therefore recomputed on the final actual itself. -/
theorem fixedGlobalMatterDualFullCauchy_torsionSpin_origin :
    internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe
              0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt
                positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe
                0)
              (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.gravityConnection
                0))) =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus
              positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual)
            0) := by
  let previous :=
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
  let final :=
    positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource previous final 0
      (congrFun fixedGlobalMatterDualFullCauchy_coframe.symm 0)
      fixedGlobalMatterDualFullCauchy_matter_origin_eq_previous.symm
      fixedGlobalMatterDualFullCauchy_conjugate_origin_eq_previous.symm
  change
    formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus previous) 0) =
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus final) 0) at spinEq
  change
    internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (final.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt final.coframe 0)
              (final.gravityConnection 0))) =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus final) 0)
  calc
    _ =
        internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (previous.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt previous.coframe 0)
              (previous.gravityConnection 0))) := by
      rw [show final.coframe = previous.coframe by
        exact fixedGlobalMatterDualFullCauchy_coframe,
        show final.gravityConnection 0 = previous.gravityConnection 0 by
          exact
            fixedGlobalMatterDualFullCauchy_gravityConnection_origin_eq_previous]
    _ =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus previous) 0) :=
      fixedGlobalFullCauchy_torsionSpin_origin
    _ = _ := spinEq

/-! ## Fixed-lineage synchronization checkpoint -/

/-- One no-premise fixed-lineage output now carries the fresh primal
Dirac equation, the unique adjoint evolution law, and the recomputed Cartan
and full EC equations.  The adjoint item is deliberately stated as its
action evolution law.  The downstream fixed-lineage adjoint-acceptance module
uses the just-proved zero coframe first jet to read the densitized
Euler--Lagrange coefficient; that readout is not an additional producer
input. -/
theorem fixedGlobalMatterDualFullCauchy_realizes :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.Smooth ∧
      holonomicCoframeFirstJetAt
          positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe
          0 =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet) ∧
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
            0) =
        0 ∧
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
        0
        (holonomicConjugateMatterDerivativeDual
          positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
          0 canonicalLorentzianTimeDirection) ∧
      FormNativeGravitySimplicityEquation
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual ∧
      FormNativeGravityAuxiliaryEquation
        positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual ∧
      (internalBivectorDualThreeForm
            (torsionCoframeWedgeThreeForm
              (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe
                0)
              (pointwiseCartanTorsion
                (holonomicCoframeFirstJetAt
                  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.coframe
                  0)
                (positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual.gravityConnection
                  0))) =
          formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0
            0
            (toContinuumPointField
              (restrictHolonomicConfigurationToIIPlus
                positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual)
              0)) ∧
      identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature
              positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
              0) +
          diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual =
        0 := by
  exact
    ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      fixedGlobalMatterDualFullCauchy_smooth,
      fixedGlobalMatterDualFullCauchy_coframeFirstJet_origin,
      fixedGlobalMatterDualFullCauchy_diracYukawa,
      fixedGlobalMatterDualFullCauchy_adjointActionLaw,
      fixedGlobalMatterDualFullCauchy_simplicity,
      fixedGlobalMatterDualFullCauchy_auxiliaryEquation,
      fixedGlobalMatterDualFullCauchy_torsionSpin_origin,
      fixedGlobalMatterDualFullCauchy_EC_covector_zero⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
