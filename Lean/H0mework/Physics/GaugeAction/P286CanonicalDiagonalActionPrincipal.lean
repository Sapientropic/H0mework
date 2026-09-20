import H0mework.Physics.ConnectionJets.P286ConstitutiveSecondJetResponse

/-!
# Canonical diagonal P286 action principal

The P286 connection action contracts a holonomic connection Hessian with the
positive Lie pairing.  This module exposes the canonical diagonal section of
that principal operator.  Its coefficient `-1/6` is fixed by the action
coefficient `2` and the three transverse spacetime directions; it is not a
source parameter, residual coordinate, target witness, or branch choice.

The section is faithful both as a second jet and after the existing homogeneous
quadratic realization.  Composing it with the action response gives the full
one-form pairing dual.  The latter is a finite-dimensional linear equivalence,
so an action covector determines one canonical diagonal principal increment
without taking a quotient.

This module does not install the increment in a Stage-9 current, inspect a
residual support, or claim a complete common successor.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286CanonicalDiagonalActionPrincipal

open ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ConstitutiveSecondJetResponse
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineP286SourceAffineCurvatureJetNormalForm
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Faithful action pairing -/

/-- The positive P286 pairing, applied independently in all four one-form
directions, as a linear map to the full one-form dual. -/
def p286GaugeOneFormPairingDual :
    P286GaugeOneForm →ₗ[ℝ] Module.Dual ℝ P286GaugeOneForm where
  toFun current :=
    { toFun := fun direction =>
        ∑ formDirection : LorentzianIndex,
          p286CoordinateLiePairing
            (current formDirection) (direction formDirection)
      map_add' := by
        intro first second
        simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_right,
          Finset.sum_add_distrib]
      map_smul' := by
        intro parameter direction
        simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_right]
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [Finset.mul_sum] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro direction
    change
      (∑ formDirection : LorentzianIndex,
        p286CoordinateLiePairing
          ((first + second) formDirection) (direction formDirection)) =
        (∑ formDirection : LorentzianIndex,
          p286CoordinateLiePairing
            (first formDirection) (direction formDirection)) +
          ∑ formDirection : LorentzianIndex,
            p286CoordinateLiePairing
              (second formDirection) (direction formDirection)
    simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_left,
      Finset.sum_add_distrib]
  map_smul' := by
    intro parameter current
    apply LinearMap.ext
    intro direction
    change
      (∑ formDirection : LorentzianIndex,
        p286CoordinateLiePairing
          ((parameter • current) formDirection) (direction formDirection)) =
        parameter *
          ∑ formDirection : LorentzianIndex,
            p286CoordinateLiePairing
              (current formDirection) (direction formDirection)
    simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left,
      Finset.mul_sum]

@[simp] theorem p286GaugeOneFormPairingDual_apply
    (current direction : P286GaugeOneForm) :
    p286GaugeOneFormPairingDual current direction =
      ∑ formDirection : LorentzianIndex,
        p286CoordinateLiePairing
          (current formDirection) (direction formDirection) :=
  rfl

theorem p286GaugeOneFormPairingDual_injective :
    Function.Injective p286GaugeOneFormPairingDual := by
  intro first second equality
  have differenceZero :
      p286GaugeOneFormPairingDual (first - second) = 0 := by
    rw [map_sub, equality, sub_self]
  have evaluated := congrArg
    (fun response : Module.Dual ℝ P286GaugeOneForm =>
      response (first - second))
    differenceZero
  change
    (∑ formDirection : LorentzianIndex,
      p286CoordinateLiePairing
        ((first - second) formDirection)
        ((first - second) formDirection)) = 0 at evaluated
  have eachPairingZeroWithMembership :
      ∀ formDirection ∈ (Finset.univ : Finset LorentzianIndex),
        p286CoordinateLiePairing
            ((first - second) formDirection)
            ((first - second) formDirection) =
          0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun formDirection _ =>
        p286CoordinateLiePairing_self_nonnegative
          ((first - second) formDirection))).mp evaluated
  have eachPairingZero :
      ∀ formDirection : LorentzianIndex,
        p286CoordinateLiePairing
            ((first - second) formDirection)
            ((first - second) formDirection) =
          0 := fun formDirection =>
    eachPairingZeroWithMembership formDirection (Finset.mem_univ _)
  have differenceCoordinateZero : first - second = 0 := by
    funext formDirection
    exact (p286CoordinateLiePairing_self_eq_zero_iff
      ((first - second) formDirection)).mp
        (eachPairingZero formDirection)
  exact sub_eq_zero.mp differenceCoordinateZero

theorem p286GaugeOneFormPairingDual_surjective :
    Function.Surjective p286GaugeOneFormPairingDual := by
  have dimensionEquality :
      Module.finrank ℝ P286GaugeOneForm =
        Module.finrank ℝ (Module.Dual ℝ P286GaugeOneForm) := by
    exact Subspace.dual_finrank_eq.symm
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    dimensionEquality).mp
  exact p286GaugeOneFormPairingDual_injective

/-- The full P286 one-form action pairing is nondegenerate. -/
noncomputable def p286GaugeOneFormPairingEquiv :
    P286GaugeOneForm ≃ₗ[ℝ] Module.Dual ℝ P286GaugeOneForm :=
  LinearEquiv.ofBijective p286GaugeOneFormPairingDual
    ⟨p286GaugeOneFormPairingDual_injective,
      p286GaugeOneFormPairingDual_surjective⟩

@[simp] theorem p286GaugeOneFormPairingEquiv_apply
    (current : P286GaugeOneForm) :
    p286GaugeOneFormPairingEquiv current =
      p286GaugeOneFormPairingDual current :=
  rfl

/-! ## Canonical diagonal section -/

/-- One diagonal row of the canonical action-principal Hessian.  The
normalization is the unique inverse of the action coefficient `2` summed over
the three directions transverse to the diagonal direction. -/
def p286CanonicalDiagonalResponseOneForm
    (current : P286GaugeOneForm) (diagonalDirection : LorentzianIndex) :
    P286GaugeOneForm :=
  fun formDirection =>
    if formDirection = diagonalDirection then 0
    else
      ((-1 / 6 : ℝ) *
        minkowskiInternalSign diagonalDirection *
        minkowskiInternalSign formDirection) •
          current formDirection

/-- Ambient diagonal Hessian selected by the action principal. -/
def p286CanonicalDiagonalResponseSecondJetAmbient
    (current : P286GaugeOneForm) : P286ConnectionSecondJetAmbient :=
  ∑ diagonalDirection : LorentzianIndex,
    (p286BaseCoordinate diagonalDirection).smulRight
      ((p286BaseCoordinate diagonalDirection).smulRight
        (p286CanonicalDiagonalResponseOneForm current diagonalDirection))

theorem p286CanonicalDiagonalResponseSecondJetAmbient_symmetric
    (current : P286GaugeOneForm) (first second : BasePoint) :
    p286CanonicalDiagonalResponseSecondJetAmbient current first second =
      p286CanonicalDiagonalResponseSecondJetAmbient current second first := by
  unfold p286CanonicalDiagonalResponseSecondJetAmbient
  change
    (∑ diagonalDirection : LorentzianIndex,
      first diagonalDirection •
        (second diagonalDirection •
          p286CanonicalDiagonalResponseOneForm current diagonalDirection)) =
      ∑ diagonalDirection : LorentzianIndex,
        second diagonalDirection •
          (first diagonalDirection •
            p286CanonicalDiagonalResponseOneForm current diagonalDirection)
  apply Finset.sum_congr rfl
  intro diagonalDirection _
  module

private theorem p286CanonicalDiagonalResponseOneForm_add
    (first second : P286GaugeOneForm)
    (diagonalDirection : LorentzianIndex) :
    p286CanonicalDiagonalResponseOneForm (first + second)
        diagonalDirection =
      p286CanonicalDiagonalResponseOneForm first diagonalDirection +
        p286CanonicalDiagonalResponseOneForm second diagonalDirection := by
  funext formDirection
  by_cases sameDirection : formDirection = diagonalDirection
  · simp [p286CanonicalDiagonalResponseOneForm, sameDirection]
  · simp [p286CanonicalDiagonalResponseOneForm, sameDirection,
      Pi.add_apply]

private theorem p286CanonicalDiagonalResponseOneForm_smul
    (parameter : ℝ) (current : P286GaugeOneForm)
    (diagonalDirection : LorentzianIndex) :
    p286CanonicalDiagonalResponseOneForm (parameter • current)
        diagonalDirection =
      parameter •
        p286CanonicalDiagonalResponseOneForm current diagonalDirection := by
  funext formDirection
  by_cases sameDirection : formDirection = diagonalDirection
  · simp [p286CanonicalDiagonalResponseOneForm, sameDirection]
  · simp [p286CanonicalDiagonalResponseOneForm, sameDirection,
      Pi.smul_apply]
    module

private theorem p286CanonicalDiagonalResponseSecondJetAmbient_add
    (first second : P286GaugeOneForm) :
    p286CanonicalDiagonalResponseSecondJetAmbient (first + second) =
      p286CanonicalDiagonalResponseSecondJetAmbient first +
        p286CanonicalDiagonalResponseSecondJetAmbient second := by
  apply ContinuousLinearMap.ext
  intro outer
  apply ContinuousLinearMap.ext
  intro inner
  unfold p286CanonicalDiagonalResponseSecondJetAmbient
  change
    (∑ diagonalDirection : LorentzianIndex,
      outer diagonalDirection •
        (inner diagonalDirection •
          p286CanonicalDiagonalResponseOneForm (first + second)
            diagonalDirection)) =
      (∑ diagonalDirection : LorentzianIndex,
        outer diagonalDirection •
          (inner diagonalDirection •
            p286CanonicalDiagonalResponseOneForm first
              diagonalDirection)) +
        ∑ diagonalDirection : LorentzianIndex,
          outer diagonalDirection •
            (inner diagonalDirection •
              p286CanonicalDiagonalResponseOneForm second
                diagonalDirection)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro diagonalDirection _
  rw [p286CanonicalDiagonalResponseOneForm_add]
  module

private theorem p286CanonicalDiagonalResponseSecondJetAmbient_smul
    (parameter : ℝ) (current : P286GaugeOneForm) :
    p286CanonicalDiagonalResponseSecondJetAmbient (parameter • current) =
      parameter •
        p286CanonicalDiagonalResponseSecondJetAmbient current := by
  apply ContinuousLinearMap.ext
  intro outer
  apply ContinuousLinearMap.ext
  intro inner
  unfold p286CanonicalDiagonalResponseSecondJetAmbient
  change
    (∑ diagonalDirection : LorentzianIndex,
      outer diagonalDirection •
        (inner diagonalDirection •
          p286CanonicalDiagonalResponseOneForm (parameter • current)
            diagonalDirection)) =
      parameter •
        ∑ diagonalDirection : LorentzianIndex,
          outer diagonalDirection •
            (inner diagonalDirection •
              p286CanonicalDiagonalResponseOneForm current
                diagonalDirection)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro diagonalDirection _
  rw [p286CanonicalDiagonalResponseOneForm_smul]
  module

/-- Canonical no-parameter diagonal section from a P286 one-form action
coordinate to a holonomic connection Hessian. -/
def p286CanonicalDiagonalResponseSecondJet :
    P286GaugeOneForm →ₗ[ℝ] P286HolonomicConnectionSecondJet where
  toFun current :=
    ⟨p286CanonicalDiagonalResponseSecondJetAmbient current,
      p286CanonicalDiagonalResponseSecondJetAmbient_symmetric current⟩
  map_add' := by
    intro first second
    apply Subtype.ext
    exact p286CanonicalDiagonalResponseSecondJetAmbient_add first second
  map_smul' := by
    intro parameter current
    apply Subtype.ext
    exact p286CanonicalDiagonalResponseSecondJetAmbient_smul parameter current

@[simp] theorem p286CanonicalDiagonalResponseSecondJet_apply
    (current : P286GaugeOneForm) :
    (p286CanonicalDiagonalResponseSecondJet current).1 =
      p286CanonicalDiagonalResponseSecondJetAmbient current :=
  rfl

/-- Exact action response of the canonical diagonal Hessian. -/
theorem p286CanonicalDiagonalResponseSecondJet_response
    (current direction : P286GaugeOneForm) :
    p286HolonomicSecondJetEulerLagrangeResponse
        (p286CanonicalDiagonalResponseSecondJet current) direction =
      p286GaugeOneFormPairingDual current direction := by
  rw [p286HolonomicSecondJetEulerLagrangeResponse_apply]
  unfold p286HolonomicSecondJetBFDivergenceResponseValue
  rw [Fin.sum_univ_four]
  simp_rw [p286HolonomicSecondJetBFDivergenceResponseTerm_normalForm,
    Fin.sum_univ_six]
  simp [p286CanonicalDiagonalResponseSecondJet,
    p286CanonicalDiagonalResponseSecondJetAmbient,
    p286CanonicalDiagonalResponseOneForm,
    p286HolonomicSecondJetCurvatureSymbol,
    p286HolonomicSecondJetOrderedCurvatureSymbol,
    p286GaugeExteriorDerivativeDirection,
    p286GaugeOneFormPairingDual,
    Fin.sum_univ_four,
    ContinuousLinearMap.smulRight_apply,
    p286BaseCoordinate_apply, coordinateDirection,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_neg_left_local,
    p286CoordinateLiePairing_neg_right_local]
  ring

/-- The canonical diagonal section intertwines the action response with the
nondegenerate one-form pairing. -/
theorem p286HolonomicSecondJetEulerLagrangeResponse_comp_canonicalDiagonal :
    p286HolonomicSecondJetEulerLagrangeResponse.comp
        p286CanonicalDiagonalResponseSecondJet =
      p286GaugeOneFormPairingDual := by
  apply LinearMap.ext
  intro current
  apply LinearMap.ext
  intro direction
  exact p286CanonicalDiagonalResponseSecondJet_response current direction

theorem p286CanonicalDiagonalResponseSecondJet_injective :
    Function.Injective p286CanonicalDiagonalResponseSecondJet := by
  intro first second equality
  apply p286GaugeOneFormPairingDual_injective
  apply LinearMap.ext
  intro direction
  calc
    p286GaugeOneFormPairingDual first direction =
        p286HolonomicSecondJetEulerLagrangeResponse
          (p286CanonicalDiagonalResponseSecondJet first) direction :=
      (p286CanonicalDiagonalResponseSecondJet_response first direction).symm
    _ = p286HolonomicSecondJetEulerLagrangeResponse
          (p286CanonicalDiagonalResponseSecondJet second) direction := by
      rw [equality]
    _ = p286GaugeOneFormPairingDual second direction :=
      p286CanonicalDiagonalResponseSecondJet_response second direction

theorem p286CanonicalDiagonalResponseSecondJet_eq_iff
    (first second : P286GaugeOneForm) :
    p286CanonicalDiagonalResponseSecondJet first =
        p286CanonicalDiagonalResponseSecondJet second ↔
      first = second := by
  constructor
  · intro equality
    exact p286CanonicalDiagonalResponseSecondJet_injective equality
  · intro equality
    rw [equality]

/-! ## Faithful quadratic increment -/

/-- The actual homogeneous-quadratic connection increment generated by the
canonical diagonal action principal. -/
def p286CanonicalDiagonalActionPrincipalQuadraticIncrement :
    P286GaugeOneForm →ₗ[ℝ] (BasePoint → P286GaugeOneForm) :=
  p286HolonomicSecondJetQuadraticRealization.comp
    p286CanonicalDiagonalResponseSecondJet

theorem p286CanonicalDiagonalActionPrincipalQuadraticIncrement_injective :
    Function.Injective
      p286CanonicalDiagonalActionPrincipalQuadraticIncrement := by
  intro first second equality
  apply p286CanonicalDiagonalResponseSecondJet_injective
  apply p286HolonomicSecondJetQuadraticRealization_injective
  exact equality

/-! ## Direct action-covector section -/

/-- Canonical diagonal Hessian generated from a full P286 action covector.
The inverse used here is the nondegenerate action pairing, not a response
quotient or an arbitrary Hessian preimage. -/
noncomputable def p286CanonicalDiagonalActionPrincipalSection :
    Module.Dual ℝ P286GaugeOneForm →ₗ[ℝ]
      P286HolonomicConnectionSecondJet :=
  p286CanonicalDiagonalResponseSecondJet.comp
    p286GaugeOneFormPairingEquiv.symm.toLinearMap

/-- The action-principal section is a right inverse of the complete P286
second-jet action response. -/
theorem p286HolonomicSecondJetEulerLagrangeResponse_comp_actionPrincipalSection :
    p286HolonomicSecondJetEulerLagrangeResponse.comp
        p286CanonicalDiagonalActionPrincipalSection =
      LinearMap.id := by
  apply LinearMap.ext
  intro actionCovector
  change
    p286HolonomicSecondJetEulerLagrangeResponse
        (p286CanonicalDiagonalResponseSecondJet
          (p286GaugeOneFormPairingEquiv.symm actionCovector)) =
      actionCovector
  apply LinearMap.ext
  intro direction
  rw [p286CanonicalDiagonalResponseSecondJet_response]
  have pairingEquality :=
    p286GaugeOneFormPairingEquiv.apply_symm_apply actionCovector
  exact congrArg
    (fun response : Module.Dual ℝ P286GaugeOneForm => response direction)
    pairingEquality

theorem p286CanonicalDiagonalActionPrincipalSection_injective :
    Function.Injective p286CanonicalDiagonalActionPrincipalSection := by
  intro first second equality
  have responseEquality := congrArg
    p286HolonomicSecondJetEulerLagrangeResponse equality
  have firstResponse :
      p286HolonomicSecondJetEulerLagrangeResponse
          (p286CanonicalDiagonalActionPrincipalSection first) =
        first := by
    have mapEquality := congrArg
      (fun response :
          Module.Dual ℝ P286GaugeOneForm →ₗ[ℝ]
            Module.Dual ℝ P286GaugeOneForm =>
        response first)
      p286HolonomicSecondJetEulerLagrangeResponse_comp_actionPrincipalSection
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using mapEquality
  have secondResponse :
      p286HolonomicSecondJetEulerLagrangeResponse
          (p286CanonicalDiagonalActionPrincipalSection second) =
        second := by
    have mapEquality := congrArg
      (fun response :
          Module.Dual ℝ P286GaugeOneForm →ₗ[ℝ]
            Module.Dual ℝ P286GaugeOneForm =>
        response second)
      p286HolonomicSecondJetEulerLagrangeResponse_comp_actionPrincipalSection
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using mapEquality
  exact firstResponse.symm.trans (responseEquality.trans secondResponse)

end

end SaturationMonoid.PhysicsCore.StageNineP286CanonicalDiagonalActionPrincipal
