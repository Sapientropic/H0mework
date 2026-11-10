import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.StageNinePlebanskiInternalMultiplierCarrier
import H0mework.Physics.MatterCurrent.LinearPlebanskiLocalActualLift
import H0mework.Physics.MatterCurrent.FullSynchronizedResponseLocalActualLift
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermDecision
import H0mework.Physics.Coframe.ResidualLimitCoframeBalanceDecision

/-!
# J1.5: existing gravity-multiplier reaction-image compatibility

This module tests the existing 36-coordinate gravity field against the
standard nonchiral Plebanski multiplier carrier without renaming that field
or selecting the authoritative root action.

The `φ`-dependent term in the standard diagnostic `δB` convention is the typed reaction
`Phi_φ(B) = φ * B`.  On a nondegenerate `B`, right multiplication by `B`
is inverted by the actual matrix inverse.  This fixes the direction of the
reaction map independently of the fixed candidate; no residual, projection,
source value, branch choice, or supplied shell certificate enters the
inverse.

For the identity `II+` bivector, the module then consumes the multiplier
actually installed in the final synchronized P506 current `U*`, not the
earlier matter-only multiplier.  Its reconstructed ambient multiplier has
coordinates `(3,4) = -5/16` and `(4,3) = 5/16`, so it violates
pair-exchange symmetry.  Thus, if this old field is interpreted as the entire
`δB` reaction, it cannot be a pure reaction image of any standard
trace-restricted multiplier.  The theorem does not exclude additional action
legs or select between standard-quadratic and residual-linear formulations.

The allowed projection and its complement are diagnostics.  Their zero
fiber is exactly standard-carrier membership.  Spin transport is stated only
after proving that reconstruction commutes with the actual transformed `B`
and reaction, and only as faithful zero-fiber transport.  None of these
results produces a repair field, proves the authoritative root shell empty,
or changes source data.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNinePlebanskiExistingGravityMultiplierCompatibility

open ProofFreeRicherAnholonomicSource
open StageNineCartanTangentSimplicityResponse
open StageNineBlockwiseConstitutive
open StageNineGlobalBundle
open StageNineGlobalIntegratedAction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNinePlebanskiInternalMultiplierCarrier
open StageNinePhysicalBivectorSpinRepresentation
open StageNineResidualLimitCoframeBalanceDecision
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermDecision
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress
open StageNineSpinMatterBundle

noncomputable section

set_option autoImplicit false

def physicalBivectorMatrix (bivector : PhysicalBivector) :
    InternalPairTensor :=
  fun internalPair spacetimePair => bivector internalPair spacetimePair

abbrev PlebanskiBReaction := InternalPairTensor

def standardPlebanskiReaction
    (multiplier : StandardPlebanskiMultiplier)
    (bivector : PhysicalBivector) : PlebanskiBReaction :=
  (multiplier : InternalPairTensor) * physicalBivectorMatrix bivector

def rawPlebanskiMultiplierCandidate
    (bivector : PhysicalBivector) (reaction : PlebanskiBReaction) :
    InternalPairTensor :=
  reaction * (physicalBivectorMatrix bivector)⁻¹

theorem rawPlebanskiMultiplierCandidate_reaction
    (multiplier : StandardPlebanskiMultiplier)
    (bivector : PhysicalBivector)
    (nondegenerate : Matrix.det bivector ≠ 0) :
    rawPlebanskiMultiplierCandidate bivector
        (standardPlebanskiReaction multiplier bivector) =
      (multiplier : InternalPairTensor) := by
  rw [rawPlebanskiMultiplierCandidate, standardPlebanskiReaction]
  change ((multiplier : InternalPairTensor) *
      physicalBivectorMatrix bivector) *
        (physicalBivectorMatrix bivector)⁻¹ = multiplier
  rw [
    Matrix.mul_assoc,
    Matrix.mul_nonsing_inv (physicalBivectorMatrix bivector)
      (isUnit_iff_ne_zero.mpr nondegenerate),
    Matrix.mul_one]

theorem standardPlebanskiReaction_candidate
    (bivector : PhysicalBivector) (reaction : PlebanskiBReaction)
    (nondegenerate : Matrix.det bivector ≠ 0) :
    rawPlebanskiMultiplierCandidate bivector reaction *
        physicalBivectorMatrix bivector =
      reaction := by
  change (reaction *
      (physicalBivectorMatrix bivector)⁻¹) *
        physicalBivectorMatrix bivector = reaction
  rw [Matrix.mul_assoc,
    Matrix.nonsing_inv_mul (physicalBivectorMatrix bivector)
      (isUnit_iff_ne_zero.mpr nondegenerate), Matrix.mul_one]

def spinPlebanskiReactionLinearEquiv (groupElement : SpinPlus13) :
    PlebanskiBReaction ≃ₗ[ℝ] PlebanskiBReaction where
  toFun reaction :=
    Matrix.transpose
        (coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹)) * reaction
  invFun reaction :=
    Matrix.transpose
        (coframeTwoFormMatrix (spinLorentzMatrix groupElement)) * reaction
  left_inv := by
    intro reaction
    change Matrix.transpose
        (coframeTwoFormMatrix (spinLorentzMatrix groupElement)) *
      (Matrix.transpose
        (coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹)) *
          reaction) = reaction
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← coframeTwoFormMatrix_mul, ← map_mul spinLorentzMatrix]
    simp
  right_inv := by
    intro reaction
    change Matrix.transpose
        (coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹)) *
      (Matrix.transpose
        (coframeTwoFormMatrix (spinLorentzMatrix groupElement)) *
          reaction) = reaction
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← coframeTwoFormMatrix_mul, ← map_mul spinLorentzMatrix]
    simp
  map_add' := by
    intro first second
    exact Matrix.mul_add _ _ _
  map_smul' := by
    intro scalar reaction
    simp

@[simp] theorem spinPlebanskiReactionLinearEquiv_apply
    (groupElement : SpinPlus13) (reaction : PlebanskiBReaction) :
    spinPlebanskiReactionLinearEquiv groupElement reaction =
      Matrix.transpose
          (coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹)) *
        reaction :=
  rfl

def spinPlebanskiReactionRepresentation :
    SpinPlus13 →* (PlebanskiBReaction ≃ₗ[ℝ] PlebanskiBReaction) where
  toFun := spinPlebanskiReactionLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro reaction
    simp [spinPlebanskiReactionLinearEquiv]
  map_mul' first second := by
    apply LinearEquiv.ext
    intro reaction
    change Matrix.transpose
          (coframeTwoFormMatrix (spinLorentzMatrix (first * second)⁻¹)) *
        reaction =
      Matrix.transpose
          (coframeTwoFormMatrix (spinLorentzMatrix first⁻¹)) *
        (Matrix.transpose
          (coframeTwoFormMatrix (spinLorentzMatrix second⁻¹)) * reaction)
    rw [mul_inv_rev, map_mul spinLorentzMatrix,
      coframeTwoFormMatrix_mul, Matrix.transpose_mul,
      Matrix.mul_assoc]

theorem physicalBivectorMatrix_spinLorentzPhysicalBivectorLinearEquiv
    (groupElement : SpinPlus13) (bivector : PhysicalBivector) :
    physicalBivectorMatrix
        (spinLorentzPhysicalBivectorLinearEquiv groupElement bivector) =
      coframeTwoFormMatrix (spinLorentzMatrix groupElement) *
        physicalBivectorMatrix bivector := by
  ext internalPair spacetimePair
  change spinLorentzPhysicalBivectorLinearEquiv groupElement bivector
      internalPair spacetimePair = _
  rw [spinLorentzPhysicalBivectorLinearEquiv_apply]
  change coframeTwoFormLinear (spinLorentzMatrix groupElement)
      (fun sourceInternalPair => bivector sourceInternalPair spacetimePair)
        internalPair = _
  simp [coframeTwoFormLinear, coframeTwoFormMatrix,
    physicalBivectorMatrix, Matrix.mul_apply]

theorem standardPlebanskiReaction_spin_covariant
    (groupElement : SpinPlus13)
    (multiplier : StandardPlebanskiMultiplier)
    (bivector : PhysicalBivector) :
    standardPlebanskiReaction
        (standardPlebanskiMultiplierSpinLinearEquiv groupElement multiplier)
        (spinLorentzPhysicalBivectorLinearEquiv groupElement bivector) =
      spinPlebanskiReactionLinearEquiv groupElement
        (standardPlebanskiReaction multiplier bivector) := by
  rw [standardPlebanskiReaction, standardPlebanskiReaction,
    standardPlebanskiMultiplierSpinLinearEquiv_apply,
    rawMultiplierSpinLinearEquiv_apply,
    physicalBivectorMatrix_spinLorentzPhysicalBivectorLinearEquiv,
    spinPlebanskiReactionLinearEquiv_apply]
  unfold pullbackTensor
  have cancellation :
      coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹) *
          coframeTwoFormMatrix (spinLorentzMatrix groupElement) =
        1 := by
    rw [← coframeTwoFormMatrix_mul, ← map_mul spinLorentzMatrix]
    simp
  rw [show
      (Matrix.transpose
          (coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹)) *
        (multiplier : InternalPairTensor) *
          coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹)) *
        (coframeTwoFormMatrix (spinLorentzMatrix groupElement) *
          physicalBivectorMatrix bivector) =
      Matrix.transpose
          (coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹)) *
        (multiplier : InternalPairTensor) *
          (coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹) *
            coframeTwoFormMatrix (spinLorentzMatrix groupElement)) *
              physicalBivectorMatrix bivector by
    simp only [Matrix.mul_assoc]]
  rw [cancellation]
  simp [Matrix.mul_assoc]

/-- Reconstructing the ambient multiplier from a transformed `B` and its
transformed `δB` reaction commutes with the actual two-leg Spin action. -/
theorem rawPlebanskiMultiplierCandidate_spin_covariant
    (groupElement : SpinPlus13)
    (bivector : PhysicalBivector)
    (reaction : PlebanskiBReaction) :
    rawPlebanskiMultiplierCandidate
        (spinLorentzPhysicalBivectorLinearEquiv groupElement bivector)
        (spinPlebanskiReactionLinearEquiv groupElement reaction) =
      rawMultiplierSpinLinearEquiv groupElement
        (rawPlebanskiMultiplierCandidate bivector reaction) := by
  rw [rawPlebanskiMultiplierCandidate,
    physicalBivectorMatrix_spinLorentzPhysicalBivectorLinearEquiv,
    spinPlebanskiReactionLinearEquiv_apply,
    rawMultiplierSpinLinearEquiv_apply]
  unfold pullbackTensor
  have inverseMatrix :
      (coframeTwoFormMatrix (spinLorentzMatrix groupElement))⁻¹ =
        coframeTwoFormMatrix (spinLorentzMatrix groupElement⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [← coframeTwoFormMatrix_mul, ← map_mul spinLorentzMatrix]
    simp
  rw [Matrix.mul_inv_rev, inverseMatrix]
  simp [rawPlebanskiMultiplierCandidate, Matrix.mul_assoc]

theorem identityPhysicalIIPlusBivector_mul_self :
    physicalBivectorMatrix
        (physicalIIPlusBivector (1 : LorentzianCoframe)) *
      physicalBivectorMatrix
        (physicalIIPlusBivector (1 : LorentzianCoframe)) =
      -(1 : InternalPairTensor) := by
  rw [physicalIIPlusBivector_one_eq_identityCoordinates]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [physicalBivectorMatrix, identityPhysicalIIPlusBivector,
      Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val']

theorem identityPhysicalIIPlusBivector_inv :
    (physicalBivectorMatrix
        (physicalIIPlusBivector (1 : LorentzianCoframe)))⁻¹ =
      -physicalBivectorMatrix
        (physicalIIPlusBivector (1 : LorentzianCoframe)) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.neg_mul, identityPhysicalIIPlusBivector_mul_self]
  simp

def earlyMatterOnlyRawPlebanskiMultiplierCandidate : InternalPairTensor :=
  rawPlebanskiMultiplierCandidate
    (physicalIIPlusBivector (1 : LorentzianCoframe))
    (physicalBivectorMatrix
      positiveP506MatterCurrentLinearPlebanskiMultiplier)

theorem earlyMatterOnlyRawPlebanskiMultiplierCandidate_eq :
    earlyMatterOnlyRawPlebanskiMultiplierCandidate =
      physicalBivectorMatrix
          positiveP506MatterCurrentLinearPlebanskiMultiplier *
        (-physicalBivectorMatrix
          (physicalIIPlusBivector (1 : LorentzianCoframe))) := by
  rw [earlyMatterOnlyRawPlebanskiMultiplierCandidate,
    rawPlebanskiMultiplierCandidate,
    identityPhysicalIIPlusBivector_inv]

theorem rawCandidateOfCoframeResponse_zero_one
    (response : LorentzianCoframe) :
    rawPlebanskiMultiplierCandidate
        (physicalIIPlusBivector (1 : LorentzianCoframe))
        (physicalBivectorMatrix
          (linearPlebanskiMultiplierOfCoframeResponse response)) 0 1 =
      -response 0 3 := by
  rw [rawPlebanskiMultiplierCandidate,
    identityPhysicalIIPlusBivector_inv]
  simp [physicalBivectorMatrix,
    linearPlebanskiMultiplierOfCoframeResponse,
    physicalIIPlusCoframeTangent, coframeWedgeTangent,
    internalBivectorDual, lorentzianCoframeHodge,
    physicalIIPlusBivector, coframeWedge,
    Matrix.mul_apply, Fin.sum_univ_six,
    pairFirst, pairSecond, Matrix.one_apply]

theorem rawCandidateOfCoframeResponse_one_zero
    (response : LorentzianCoframe) :
    rawPlebanskiMultiplierCandidate
        (physicalIIPlusBivector (1 : LorentzianCoframe))
        (physicalBivectorMatrix
          (linearPlebanskiMultiplierOfCoframeResponse response)) 1 0 =
      response 0 3 := by
  rw [rawPlebanskiMultiplierCandidate,
    identityPhysicalIIPlusBivector_inv]
  simp [physicalBivectorMatrix,
    linearPlebanskiMultiplierOfCoframeResponse,
    physicalIIPlusCoframeTangent, coframeWedgeTangent,
    internalBivectorDual, lorentzianCoframeHodge,
    physicalIIPlusBivector, coframeWedge,
    Matrix.mul_apply, Fin.sum_univ_six,
    pairFirst, pairSecond, Matrix.one_apply]

theorem earlyMatterOnlyRawPlebanskiMultiplierCandidate_zero_one :
    earlyMatterOnlyRawPlebanskiMultiplierCandidate 0 1 = 1 / 16 := by
  rw [earlyMatterOnlyRawPlebanskiMultiplierCandidate,
    positiveP506MatterCurrentLinearPlebanskiMultiplier,
    rawCandidateOfCoframeResponse_zero_one,
    positiveP506MatterCurrentLinearPlebanskiCoframeResponse_selected]
  norm_num

theorem earlyMatterOnlyRawPlebanskiMultiplierCandidate_one_zero :
    earlyMatterOnlyRawPlebanskiMultiplierCandidate 1 0 = -(1 / 16) := by
  rw [earlyMatterOnlyRawPlebanskiMultiplierCandidate,
    positiveP506MatterCurrentLinearPlebanskiMultiplier,
    rawCandidateOfCoframeResponse_one_zero,
    positiveP506MatterCurrentLinearPlebanskiCoframeResponse_selected]

theorem earlyMatterOnlyRawPlebanskiMultiplierCandidate_not_isSymm :
    ¬earlyMatterOnlyRawPlebanskiMultiplierCandidate.IsSymm := by
  intro symmetric
  have coordinateEquality := symmetric.apply 0 1
  rw [earlyMatterOnlyRawPlebanskiMultiplierCandidate_zero_one,
    earlyMatterOnlyRawPlebanskiMultiplierCandidate_one_zero] at coordinateEquality
  norm_num at coordinateEquality

theorem earlyMatterOnlyRawPlebanskiMultiplierCandidate_not_mem_standardSpace :
    earlyMatterOnlyRawPlebanskiMultiplierCandidate ∉
      standardPlebanskiMultiplierSpace := by
  rw [mem_standardPlebanskiMultiplierSpace_iff]
  intro membership
  exact earlyMatterOnlyRawPlebanskiMultiplierCandidate_not_isSymm membership.1

theorem rawCandidateOfCoframeResponse_three_four
    (response : LorentzianCoframe) :
    rawPlebanskiMultiplierCandidate
        (physicalIIPlusBivector (1 : LorentzianCoframe))
        (physicalBivectorMatrix
          (linearPlebanskiMultiplierOfCoframeResponse response)) 3 4 =
      -response 3 0 := by
  rw [rawPlebanskiMultiplierCandidate,
    identityPhysicalIIPlusBivector_inv]
  simp [physicalBivectorMatrix,
    linearPlebanskiMultiplierOfCoframeResponse,
    physicalIIPlusCoframeTangent, coframeWedgeTangent,
    internalBivectorDual, lorentzianCoframeHodge,
    physicalIIPlusBivector, coframeWedge,
    Matrix.mul_apply, Fin.sum_univ_six,
    pairFirst, pairSecond, Matrix.one_apply]

theorem rawCandidateOfCoframeResponse_four_three
    (response : LorentzianCoframe) :
    rawPlebanskiMultiplierCandidate
        (physicalIIPlusBivector (1 : LorentzianCoframe))
        (physicalBivectorMatrix
          (linearPlebanskiMultiplierOfCoframeResponse response)) 4 3 =
      response 3 0 := by
  rw [rawPlebanskiMultiplierCandidate,
    identityPhysicalIIPlusBivector_inv]
  simp [physicalBivectorMatrix,
    linearPlebanskiMultiplierOfCoframeResponse,
    physicalIIPlusCoframeTangent, coframeWedgeTangent,
    internalBivectorDual, lorentzianCoframeHodge,
    physicalIIPlusBivector, coframeWedge,
    Matrix.mul_apply, Fin.sum_univ_six,
    pairFirst, pairSecond, Matrix.one_apply]

/-- The raw standard-Plebanski multiplier candidate reconstructed from the
multiplier actually installed in the final synchronized `U*`. -/
def fullSynchronizedRawPlebanskiMultiplierCandidate : InternalPairTensor :=
  rawPlebanskiMultiplierCandidate
    (physicalIIPlusBivector (1 : LorentzianCoframe))
    (physicalBivectorMatrix
      positiveP506MatterCurrentFullGravityMultiplier)

theorem fullSynchronizedGravityMultiplier_is_actual_UStar_field
    (point : BasePoint) :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravitySimplicityMultiplier
        point =
      positiveP506MatterCurrentFullGravityMultiplier :=
  rfl

/-- Exact-lineage seam: the compatibility candidate is reconstructed from
the gravity auxiliary and multiplier fields of the same final `U*` at the
same canonical contact. -/
theorem fullSynchronizedRawPlebanskiMultiplierCandidate_eq_actual_UStar :
    fullSynchronizedRawPlebanskiMultiplierCandidate =
      rawPlebanskiMultiplierCandidate
        (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityAuxiliary
          0)
        (physicalBivectorMatrix
          (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravitySimplicityMultiplier
            0)) := by
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gravityAuxiliary_simple,
    fullSynchronizedGravityMultiplier_is_actual_UStar_field]
  rfl

theorem fullSynchronizedRawPlebanskiMultiplierCandidate_three_four :
    fullSynchronizedRawPlebanskiMultiplierCandidate 3 4 =
      -(5 / 16 : ℝ) := by
  rw [fullSynchronizedRawPlebanskiMultiplierCandidate,
    positiveP506MatterCurrentFullGravityMultiplier,
    gravityCoupledLinearPlebanskiMultiplier,
    rawCandidateOfCoframeResponse_three_four,
    positiveP506MatterCurrentFullCoframeResponse_temporalSpatial30_eq_5_div_16]

theorem fullSynchronizedRawPlebanskiMultiplierCandidate_four_three :
    fullSynchronizedRawPlebanskiMultiplierCandidate 4 3 =
      (5 / 16 : ℝ) := by
  rw [fullSynchronizedRawPlebanskiMultiplierCandidate,
    positiveP506MatterCurrentFullGravityMultiplier,
    gravityCoupledLinearPlebanskiMultiplier,
    rawCandidateOfCoframeResponse_four_three,
    positiveP506MatterCurrentFullCoframeResponse_temporalSpatial30_eq_5_div_16]

theorem fullSynchronizedRawPlebanskiMultiplierCandidate_not_isSymm :
    ¬fullSynchronizedRawPlebanskiMultiplierCandidate.IsSymm := by
  intro symmetric
  have coordinateEquality := symmetric.apply 3 4
  rw [fullSynchronizedRawPlebanskiMultiplierCandidate_three_four,
    fullSynchronizedRawPlebanskiMultiplierCandidate_four_three]
    at coordinateEquality
  norm_num at coordinateEquality

theorem fullSynchronizedRawPlebanskiMultiplierCandidate_not_mem_standardSpace :
    fullSynchronizedRawPlebanskiMultiplierCandidate ∉
      standardPlebanskiMultiplierSpace := by
  rw [mem_standardPlebanskiMultiplierSpace_iff]
  intro membership
  exact fullSynchronizedRawPlebanskiMultiplierCandidate_not_isSymm membership.1

theorem identityPhysicalIIPlusBivector_det_ne_zero :
    Matrix.det
        (physicalBivectorMatrix
          (physicalIIPlusBivector (1 : LorentzianCoframe))) ≠ 0 := by
  have leftInverse :
      (-physicalBivectorMatrix
          (physicalIIPlusBivector (1 : LorentzianCoframe))) *
        physicalBivectorMatrix
          (physicalIIPlusBivector (1 : LorentzianCoframe)) = 1 := by
    rw [Matrix.neg_mul, identityPhysicalIIPlusBivector_mul_self]
    simp
  exact (Matrix.isUnit_det_of_left_inverse leftInverse).ne_zero

/-- If the old reaction installed in the final synchronized `U*` is taken as
the entire `δB` reaction, it is not the pure reaction image of any standard
trace-restricted Plebanski multiplier at its actual identity `II+` bivector. -/
theorem no_standardPlebanskiMultiplier_generates_fullSynchronizedReaction :
    ¬ ∃ multiplier : StandardPlebanskiMultiplier,
      standardPlebanskiReaction multiplier
          (physicalIIPlusBivector (1 : LorentzianCoframe)) =
        physicalBivectorMatrix
          positiveP506MatterCurrentFullGravityMultiplier := by
  rintro ⟨multiplier, reactionEquality⟩
  have candidateEquality :
      fullSynchronizedRawPlebanskiMultiplierCandidate =
        (multiplier : InternalPairTensor) := by
    rw [fullSynchronizedRawPlebanskiMultiplierCandidate,
      ← reactionEquality]
    exact rawPlebanskiMultiplierCandidate_reaction multiplier _
      identityPhysicalIIPlusBivector_det_ne_zero
  apply fullSynchronizedRawPlebanskiMultiplierCandidate_not_mem_standardSpace
  rw [candidateEquality]
  exact multiplier.property

def pairExchangeSymmetrization
    (tensor : InternalPairTensor) : InternalPairTensor :=
  (1 / 2 : ℝ) • (tensor + tensor.transpose)

theorem pairExchangeSymmetrization_isSymm
    (tensor : InternalPairTensor) :
    (pairExchangeSymmetrization tensor).IsSymm := by
  apply Matrix.IsSymm.ext
  intro firstPair secondPair
  simp [pairExchangeSymmetrization, Matrix.transpose_apply]
  ring

def standardPlebanskiAllowedProjection
    (tensor : InternalPairTensor) : InternalPairTensor :=
  pairExchangeSymmetrization tensor -
    (epsilonTrace (pairExchangeSymmetrization tensor) / 6) •
      contravariantEpsilonPairTensor

theorem standardPlebanskiAllowedProjection_mem
    (tensor : InternalPairTensor) :
    standardPlebanskiAllowedProjection tensor ∈
      standardPlebanskiMultiplierSpace := by
  rw [mem_standardPlebanskiMultiplierSpace_iff]
  refine ⟨pairExchangeSymmetrization_isSymm tensor |>.sub
    (contravariantEpsilonPairTensor_isSymm.smul _), ?_⟩
  change epsilonTraceLinearMap
      (pairExchangeSymmetrization tensor -
        (epsilonTrace (pairExchangeSymmetrization tensor) / 6) •
          contravariantEpsilonPairTensor) = 0
  rw [map_sub, map_smul]
  change epsilonTrace (pairExchangeSymmetrization tensor) -
      (epsilonTrace (pairExchangeSymmetrization tensor) / 6) *
        epsilonTrace contravariantEpsilonPairTensor = 0
  rw [epsilonTrace_contravariantEpsilonPairTensor]
  ring

theorem standardPlebanskiAllowedProjection_eq_self_of_mem
    (tensor : InternalPairTensor)
    (membership : tensor ∈ standardPlebanskiMultiplierSpace) :
    standardPlebanskiAllowedProjection tensor = tensor := by
  rw [mem_standardPlebanskiMultiplierSpace_iff] at membership
  have symmetrizationEq : pairExchangeSymmetrization tensor = tensor := by
    rw [pairExchangeSymmetrization, membership.1.eq]
    module
  rw [standardPlebanskiAllowedProjection, symmetrizationEq, membership.2]
  simp

def standardPlebanskiCompatibilityResidual
    (tensor : InternalPairTensor) : InternalPairTensor :=
  tensor - standardPlebanskiAllowedProjection tensor

theorem standardPlebanskiCompatibility_decomposition
    (tensor : InternalPairTensor) :
    tensor = standardPlebanskiAllowedProjection tensor +
      standardPlebanskiCompatibilityResidual tensor := by
  simp [standardPlebanskiCompatibilityResidual]

theorem standardPlebanskiCompatibilityResidual_eq_zero_iff
    (tensor : InternalPairTensor) :
    standardPlebanskiCompatibilityResidual tensor = 0 ↔
      tensor ∈ standardPlebanskiMultiplierSpace := by
  constructor
  · intro residualZero
    have tensorEqProjection :
        tensor = standardPlebanskiAllowedProjection tensor :=
      sub_eq_zero.mp residualZero
    rw [tensorEqProjection]
    exact standardPlebanskiAllowedProjection_mem tensor
  · intro membership
    rw [standardPlebanskiCompatibilityResidual,
      standardPlebanskiAllowedProjection_eq_self_of_mem tensor membership,
      sub_self]

theorem rawMultiplierSpinLinearEquiv_mem_standardSpace_iff
    (groupElement : SpinPlus13) (tensor : InternalPairTensor) :
    rawMultiplierSpinLinearEquiv groupElement tensor ∈
        standardPlebanskiMultiplierSpace ↔
      tensor ∈ standardPlebanskiMultiplierSpace := by
  constructor
  · intro transportedMembership
    have inverseTransportedMembership :=
      rawMultiplierSpinLinearEquiv_preserves_standardSpace groupElement⁻¹
        (rawMultiplierSpinLinearEquiv groupElement tensor)
        transportedMembership
    have inverseTransport :
        rawMultiplierSpinLinearEquiv groupElement⁻¹
            (rawMultiplierSpinLinearEquiv groupElement tensor) =
          tensor := by
      rw [rawMultiplierSpinLinearEquiv_apply,
        rawMultiplierSpinLinearEquiv_apply, inv_inv,
        pullbackTensor_comp, ← map_mul spinLorentzMatrix]
      simp [pullbackTensor]
    rwa [inverseTransport] at inverseTransportedMembership
  · exact rawMultiplierSpinLinearEquiv_preserves_standardSpace
      groupElement tensor

theorem standardPlebanskiCompatibilityResidual_spin_zero_iff
    (groupElement : SpinPlus13) (tensor : InternalPairTensor) :
    standardPlebanskiCompatibilityResidual
          (rawMultiplierSpinLinearEquiv groupElement tensor) = 0 ↔
      standardPlebanskiCompatibilityResidual tensor = 0 := by
  rw [standardPlebanskiCompatibilityResidual_eq_zero_iff,
    standardPlebanskiCompatibilityResidual_eq_zero_iff]
  exact rawMultiplierSpinLinearEquiv_mem_standardSpace_iff
    groupElement tensor

theorem reconstructedCompatibilityResidual_spin_zero_iff
    (groupElement : SpinPlus13)
    (bivector : PhysicalBivector)
    (reaction : PlebanskiBReaction) :
    standardPlebanskiCompatibilityResidual
          (rawPlebanskiMultiplierCandidate
            (spinLorentzPhysicalBivectorLinearEquiv groupElement bivector)
            (spinPlebanskiReactionLinearEquiv groupElement reaction)) = 0 ↔
      standardPlebanskiCompatibilityResidual
          (rawPlebanskiMultiplierCandidate bivector reaction) = 0 := by
  rw [rawPlebanskiMultiplierCandidate_spin_covariant]
  exact standardPlebanskiCompatibilityResidual_spin_zero_iff
    groupElement _

theorem earlyMatterOnlyRawPlebanskiMultiplierCandidate_pairExchangeDefect :
    pairExchangeDefect earlyMatterOnlyRawPlebanskiMultiplierCandidate 0 1 =
      -(1 / 8 : ℝ) := by
  change earlyMatterOnlyRawPlebanskiMultiplierCandidate 1 0 -
      earlyMatterOnlyRawPlebanskiMultiplierCandidate 0 1 = -(1 / 8 : ℝ)
  rw [earlyMatterOnlyRawPlebanskiMultiplierCandidate_one_zero,
    earlyMatterOnlyRawPlebanskiMultiplierCandidate_zero_one]
  norm_num

theorem earlyMatterOnlyStandardPlebanskiCompatibilityResidual_nonzero :
    standardPlebanskiCompatibilityResidual
        earlyMatterOnlyRawPlebanskiMultiplierCandidate ≠ 0 := by
  intro residualZero
  have membership :=
    (standardPlebanskiCompatibilityResidual_eq_zero_iff
      earlyMatterOnlyRawPlebanskiMultiplierCandidate).1 residualZero
  exact earlyMatterOnlyRawPlebanskiMultiplierCandidate_not_mem_standardSpace
    membership

theorem fullSynchronizedRawPlebanskiMultiplierCandidate_pairExchangeDefect :
    pairExchangeDefect fullSynchronizedRawPlebanskiMultiplierCandidate 3 4 =
      (5 / 8 : ℝ) := by
  change fullSynchronizedRawPlebanskiMultiplierCandidate 4 3 -
      fullSynchronizedRawPlebanskiMultiplierCandidate 3 4 = (5 / 8 : ℝ)
  rw [fullSynchronizedRawPlebanskiMultiplierCandidate_four_three,
    fullSynchronizedRawPlebanskiMultiplierCandidate_three_four]
  norm_num

/-- This `E03`-direction pair-exchange scalar is exactly the matching actual
non-gravity coframe load that the historical residual-linear multiplier was
constructed to cancel. -/
theorem fullSynchronized_pairExchangeDefect_eq_nonGravityCoframeStress :
    pairExchangeDefect fullSynchronizedRawPlebanskiMultiplierCandidate 3 4 =
      positiveP506MatterCurrentFullNonGravityCoframeStress
        temporalSpatial03CoframeVariation := by
  rw [fullSynchronizedRawPlebanskiMultiplierCandidate_pairExchangeDefect,
    positiveP506MatterCurrentFullNonGravityCoframeStress_temporalSpatial03]

/-- The same obstruction is the negative historical coframe principal.  It
therefore diagnoses an action-jurisdiction mismatch, not broken source
provenance and not a new physical residual carrier. -/
theorem fullSynchronized_pairExchangeDefect_eq_neg_linearCoframePrincipal :
    pairExchangeDefect fullSynchronizedRawPlebanskiMultiplierCandidate 3 4 =
      -linearPlebanskiCoframePrincipal
        positiveP506MatterCurrentFullCoframeResponse
        temporalSpatial03CoframeVariation := by
  rw [fullSynchronizedRawPlebanskiMultiplierCandidate_pairExchangeDefect,
    temporalSpatial03CoframeVariation,
    linearPlebanskiCoframePrincipal_coordinateDirection,
    positiveP506MatterCurrentFullCoframeResponse_temporalSpatial30_eq_5_div_16]
  simp only [if_neg (by decide : (0 : Fin 4) ≠ 3)]
  norm_num

theorem fullSynchronizedStandardPlebanskiCompatibilityResidual_nonzero :
    standardPlebanskiCompatibilityResidual
        fullSynchronizedRawPlebanskiMultiplierCandidate ≠ 0 := by
  intro residualZero
  have membership :=
    (standardPlebanskiCompatibilityResidual_eq_zero_iff
      fullSynchronizedRawPlebanskiMultiplierCandidate).1 residualZero
  exact fullSynchronizedRawPlebanskiMultiplierCandidate_not_mem_standardSpace
    membership

/-- The fixed `U*` pure-image incompatibility remains visible after
transforming its actual identity `II+` bivector and its matching reaction
together.  This is a diagnostic zero-fiber transporter, not a new equation,
repair producer, or root-formulation selector. -/
theorem fullSynchronizedCompatibilityResidual_spin_nonzero
    (groupElement : SpinPlus13) :
    standardPlebanskiCompatibilityResidual
        (rawPlebanskiMultiplierCandidate
          (spinLorentzPhysicalBivectorLinearEquiv groupElement
            (physicalIIPlusBivector (1 : LorentzianCoframe)))
          (spinPlebanskiReactionLinearEquiv groupElement
            (physicalBivectorMatrix
              positiveP506MatterCurrentFullGravityMultiplier))) ≠ 0 := by
  intro transportedZero
  have originalZero :=
    (reconstructedCompatibilityResidual_spin_zero_iff groupElement
      (physicalIIPlusBivector (1 : LorentzianCoframe))
      (physicalBivectorMatrix
        positiveP506MatterCurrentFullGravityMultiplier)).1 transportedZero
  exact fullSynchronizedStandardPlebanskiCompatibilityResidual_nonzero
    originalZero

end

end
  SaturationMonoid.PhysicsCore.StageNinePlebanskiExistingGravityMultiplierCompatibility
