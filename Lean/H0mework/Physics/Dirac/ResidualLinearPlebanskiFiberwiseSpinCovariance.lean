import H0mework.Physics.Exterior.ResidualLinearPlebanskiGlobalAction
import H0mework.Physics.Lorentz.SpinLorentzOrientation

/-!
# S9-J0-COV-0: fiberwise Spin covariance of candidate-A gravity

This module derives the algebraic Spin covariance of the residual-linear
candidate-A gravity sector.  The action on coframes and physical bivectors is
the existing action generated from the actual `SL(2,ℂ)` Spin cover.  In
particular, the simplicity multiplier transforms as a physical bivector; it
is not reinterpreted as the two-internal-leg standard Plebanski multiplier.

The orientation theorem is proved from the existing Spin definition.  The
proof reduces `SL(2,ℂ)` to its two elementary transvection families and
computes the determinant of their induced Lorentz matrices.  No determinant,
orientation, covariance, or field-equation certificate is supplied as a
premise.

The final density theorem is fiberwise: curvature is transported as an
already tensorial point-field coordinate.  It does not yet construct the
inhomogeneous local transformation of a primitive Lorentz connection, prove
holonomic curvature naturality, transport matter fields, or establish full
local-gauge covariance of the integrated unified action.  Every result here
is transporter/invariance infrastructure, not a producer or root-formulation
authority.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineResidualLinearPlebanskiFiberwiseSpinCovariance

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineSpinMatterBundle
open StageNineGlobalBundle
open StageNineLorentzCoverAndSpinDescent
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineCoframeTwoFormPairing
open StageNineResidualLinearPlebanskiGlobalAction
open StageNinePhysicalBivectorSpinRepresentation
open StageNineCoframeSpinRepresentation
open StageNineSpinLorentzOrientation
open EmpiricalReferenceScaleCouplingBoundary
open Matrix
open scoped MatrixGroups ComplexConjugate

noncomputable section

set_option autoImplicit false

/-! ## Compatibility exports for existing gravity consumers -/

/-- Compatibility alias: the representation theorem now lives in the
formulation-independent Spin--Lorentz orientation module. -/
theorem spinLorentzMatrix_det_eq_one (groupElement : SpinPlus13) :
    Matrix.det (spinLorentzMatrix groupElement) = 1 :=
  StageNineSpinLorentzOrientation.spinLorentzMatrix_det_eq_one groupElement

/-- Compatibility alias for existing gravity-sector imports. -/
theorem spinLorentzCoframe_det
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe) :
    Matrix.det (spinLorentzCoframeRepresentation groupElement coframe) =
      Matrix.det coframe :=
  StageNineSpinLorentzOrientation.spinLorentzCoframe_det groupElement coframe

/-! ## Internal Hodge and selected `II+` branch -/

private theorem upperLorentzTransvectionMatrix_hodge_commute
    (parameter : ℂ) (form : GaugeTwoForm) :
    coframeTwoFormLinear (upperLorentzTransvectionMatrix parameter)
        (lorentzianCoframeHodge form) =
      lorentzianCoframeHodge
        (coframeTwoFormLinear (upperLorentzTransvectionMatrix parameter)
          form) := by
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, coframeWedge,
      upperLorentzTransvectionMatrix, lorentzianCoframeHodge,
      pairFirst, pairSecond, Fin.sum_univ_six]
  all_goals ring

private theorem lowerLorentzTransvectionMatrix_hodge_commute
    (parameter : ℂ) (form : GaugeTwoForm) :
    coframeTwoFormLinear (lowerLorentzTransvectionMatrix parameter)
        (lorentzianCoframeHodge form) =
      lorentzianCoframeHodge
        (coframeTwoFormLinear (lowerLorentzTransvectionMatrix parameter)
          form) := by
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, coframeWedge,
      lowerLorentzTransvectionMatrix, lorentzianCoframeHodge,
      pairFirst, pairSecond, Fin.sum_univ_six]
  all_goals ring

private theorem spinLorentzTwoForm_upper_transvection_hodge_commute
    (unequal : (0 : Fin 2) ≠ 1) (parameter : ℂ)
    (form : GaugeTwoForm) :
    coframeTwoFormLinear
        (spinLorentzMatrix
          (Matrix.SpecialLinearGroup.transvection unequal parameter))
        (lorentzianCoframeHodge form) =
      lorentzianCoframeHodge
        (coframeTwoFormLinear
          (spinLorentzMatrix
            (Matrix.SpecialLinearGroup.transvection unequal parameter))
          form) := by
  rw [spinLorentzMatrix_upper_transvection]
  exact upperLorentzTransvectionMatrix_hodge_commute parameter form

private theorem spinLorentzTwoForm_lower_transvection_hodge_commute
    (unequal : (1 : Fin 2) ≠ 0) (parameter : ℂ)
    (form : GaugeTwoForm) :
    coframeTwoFormLinear
        (spinLorentzMatrix
          (Matrix.SpecialLinearGroup.transvection unequal parameter))
        (lorentzianCoframeHodge form) =
      lorentzianCoframeHodge
        (coframeTwoFormLinear
          (spinLorentzMatrix
            (Matrix.SpecialLinearGroup.transvection unequal parameter))
          form) := by
  rw [spinLorentzMatrix_lower_transvection]
  exact lowerLorentzTransvectionMatrix_hodge_commute parameter form

/-- The exterior-square action generated by the Spin cover commutes with the
fixed Lorentzian Hodge on internal two-forms. -/
theorem spinLorentzTwoForm_hodge_commute
    (groupElement : SpinPlus13) (form : GaugeTwoForm) :
    spinLorentzTwoFormRepresentation groupElement
        (lorentzianCoframeHodge form) =
      lorentzianCoframeHodge
        (spinLorentzTwoFormRepresentation groupElement form) := by
  change coframeTwoFormLinear (spinLorentzMatrix groupElement)
      (lorentzianCoframeHodge form) =
    lorentzianCoframeHodge
      (coframeTwoFormLinear (spinLorentzMatrix groupElement) form)
  revert form
  induction groupElement using Matrix.SL2.transvection_induction with
  | htransvec row column unequal parameter =>
      intro form
      fin_cases row <;> fin_cases column
      · exact False.elim (unequal rfl)
      · exact spinLorentzTwoForm_upper_transvection_hodge_commute
          unequal parameter form
      · exact spinLorentzTwoForm_lower_transvection_hodge_commute
          unequal parameter form
      · exact False.elim (unequal rfl)
  | hmul first second firstCommute secondCommute =>
      intro form
      rw [map_mul, coframeTwoFormLinear_mul]
      change coframeTwoFormLinear (spinLorentzMatrix first)
          (coframeTwoFormLinear (spinLorentzMatrix second)
            (lorentzianCoframeHodge form)) =
        lorentzianCoframeHodge
          (coframeTwoFormLinear (spinLorentzMatrix first)
            (coframeTwoFormLinear (spinLorentzMatrix second) form))
      rw [secondCommute, firstCommute]

/-- Internal Hodge transport on `PhysicalBivector` is faithful to the same
Spin action on its internal pair index. -/
theorem internalBivectorDual_spin_commute
    (groupElement : SpinPlus13) (bivector : PhysicalBivector) :
    internalBivectorDual
        (spinLorentzPhysicalBivectorRepresentation groupElement bivector) =
      spinLorentzPhysicalBivectorRepresentation groupElement
        (internalBivectorDual bivector) := by
  funext internalPair spacetimePair
  change lorentzianCoframeHodge
      (spinLorentzTwoFormRepresentation groupElement
        (fun sourceInternalPair =>
          bivector sourceInternalPair spacetimePair)) internalPair =
    spinLorentzTwoFormRepresentation groupElement
      (lorentzianCoframeHodge
        (fun sourceInternalPair =>
          bivector sourceInternalPair spacetimePair)) internalPair
  exact congrFun
    (spinLorentzTwoForm_hodge_commute groupElement
      (fun sourceInternalPair =>
        bivector sourceInternalPair spacetimePair)).symm internalPair

/-- The action-facing internal dual is the same commuting transport as the
primitive `internalBivectorDual`. -/
theorem gravityInternalDualEquiv_spin_commute
    (groupElement : SpinPlus13) (bivector : PhysicalBivector) :
    gravityInternalDualEquiv
        (spinLorentzPhysicalBivectorRepresentation groupElement bivector) =
      spinLorentzPhysicalBivectorRepresentation groupElement
        (gravityInternalDualEquiv bivector) := by
  change internalBivectorDual
      (spinLorentzPhysicalBivectorRepresentation groupElement bivector) =
    spinLorentzPhysicalBivectorRepresentation groupElement
      (internalBivectorDual bivector)
  exact internalBivectorDual_spin_commute groupElement bivector

private def gaugeTwoFormCoordinate (pair : Fin 6) : GaugeTwoForm :=
  fun candidate => if candidate = pair then 1 else 0

private theorem coframeTwoFormLinear_coordinate
    (coframe : LorentzianCoframe) (target source : Fin 6) :
    coframeTwoFormLinear coframe (gaugeTwoFormCoordinate source) target =
      coframeWedge coframe target source := by
  simp [coframeTwoFormLinear, gaugeTwoFormCoordinate]

/-- The actual coframe wedge is equivariant for the existing coframe and
physical-bivector representations. -/
theorem coframeWedge_spin_covariant
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe) :
    coframeWedge
        (spinLorentzCoframeRepresentation groupElement coframe) =
      spinLorentzPhysicalBivectorRepresentation groupElement
        (coframeWedge coframe) := by
  funext internalPair spacetimePair
  change coframeWedge (spinLorentzMatrix groupElement * coframe)
      internalPair spacetimePair =
    coframeTwoFormLinear (spinLorentzMatrix groupElement)
      (fun sourceInternalPair =>
        coframeWedge coframe sourceInternalPair spacetimePair) internalPair
  calc
    coframeWedge (spinLorentzMatrix groupElement * coframe)
        internalPair spacetimePair =
      coframeTwoFormLinear (spinLorentzMatrix groupElement * coframe)
        (gaugeTwoFormCoordinate spacetimePair) internalPair := by
          rw [coframeTwoFormLinear_coordinate]
    _ = coframeTwoFormLinear (spinLorentzMatrix groupElement)
        (coframeTwoFormLinear coframe
          (gaugeTwoFormCoordinate spacetimePair)) internalPair := by
          rw [coframeTwoFormLinear_mul]
          rfl
    _ = coframeTwoFormLinear (spinLorentzMatrix groupElement)
        (fun sourceInternalPair =>
          coframeWedge coframe sourceInternalPair spacetimePair)
        internalPair := by
          apply congrArg (fun form =>
            coframeTwoFormLinear (spinLorentzMatrix groupElement)
              form internalPair)
          funext sourceInternalPair
          exact coframeTwoFormLinear_coordinate coframe
            sourceInternalPair spacetimePair

/-- The selected physical `II+ = ⋆ᵢ(e∧e)` branch is equivariant under the
same Spin action; no standard-Plebanski multiplier carrier is involved. -/
theorem physicalIIPlusBivector_spin_covariant
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe) :
    physicalIIPlusBivector
        (spinLorentzCoframeRepresentation groupElement coframe) =
      spinLorentzPhysicalBivectorRepresentation groupElement
        (physicalIIPlusBivector coframe) := by
  unfold physicalIIPlusBivector
  rw [coframeWedge_spin_covariant, internalBivectorDual_spin_commute]

/-! ## Pairing and dynamical spacetime Hodge -/

private theorem upperLorentzTransvectionMatrix_twoFormPairing
    (parameter : ℂ) (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing 1
        (coframeTwoFormLinear (upperLorentzTransvectionMatrix parameter)
          first)
        (coframeTwoFormLinear (upperLorentzTransvectionMatrix parameter)
          second) =
      coframeTwoFormMetricPairing 1 first second := by
  unfold coframeTwoFormMetricPairing
  simp only [coframeTwoFormLinear_one, LinearMap.id_apply]
  simp [coframeTwoFormLinear,
    coframeWedge, upperLorentzTransvectionMatrix,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Fin.sum_univ_six]
  ring

private theorem lowerLorentzTransvectionMatrix_twoFormPairing
    (parameter : ℂ) (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing 1
        (coframeTwoFormLinear (lowerLorentzTransvectionMatrix parameter)
          first)
        (coframeTwoFormLinear (lowerLorentzTransvectionMatrix parameter)
          second) =
      coframeTwoFormMetricPairing 1 first second := by
  unfold coframeTwoFormMetricPairing
  simp only [coframeTwoFormLinear_one, LinearMap.id_apply]
  simp [coframeTwoFormLinear,
    coframeWedge, lowerLorentzTransvectionMatrix,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Fin.sum_univ_six]
  ring

private theorem spinLorentzTwoForm_upper_transvection_pairing
    (unequal : (0 : Fin 2) ≠ 1) (parameter : ℂ)
    (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing 1
        (coframeTwoFormLinear
          (spinLorentzMatrix
            (Matrix.SpecialLinearGroup.transvection unequal parameter))
          first)
        (coframeTwoFormLinear
          (spinLorentzMatrix
            (Matrix.SpecialLinearGroup.transvection unequal parameter))
          second) =
      coframeTwoFormMetricPairing 1 first second := by
  rw [spinLorentzMatrix_upper_transvection]
  exact upperLorentzTransvectionMatrix_twoFormPairing
    parameter first second

private theorem spinLorentzTwoForm_lower_transvection_pairing
    (unequal : (1 : Fin 2) ≠ 0) (parameter : ℂ)
    (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing 1
        (coframeTwoFormLinear
          (spinLorentzMatrix
            (Matrix.SpecialLinearGroup.transvection unequal parameter))
          first)
        (coframeTwoFormLinear
          (spinLorentzMatrix
            (Matrix.SpecialLinearGroup.transvection unequal parameter))
          second) =
      coframeTwoFormMetricPairing 1 first second := by
  rw [spinLorentzMatrix_lower_transvection]
  exact lowerLorentzTransvectionMatrix_twoFormPairing
    parameter first second

/-- The induced Spin action preserves the fixed Lorentzian two-form metric
pairing. -/
theorem spinLorentzTwoForm_pairing_invariant
    (groupElement : SpinPlus13) (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing 1
        (spinLorentzTwoFormRepresentation groupElement first)
        (spinLorentzTwoFormRepresentation groupElement second) =
      coframeTwoFormMetricPairing 1 first second := by
  change coframeTwoFormMetricPairing 1
      (coframeTwoFormLinear (spinLorentzMatrix groupElement) first)
      (coframeTwoFormLinear (spinLorentzMatrix groupElement) second) =
    coframeTwoFormMetricPairing 1 first second
  revert first second
  induction groupElement using Matrix.SL2.transvection_induction with
  | htransvec row column unequal parameter =>
      intro first second
      fin_cases row <;> fin_cases column
      · exact False.elim (unequal rfl)
      · exact spinLorentzTwoForm_upper_transvection_pairing
          unequal parameter first second
      · exact spinLorentzTwoForm_lower_transvection_pairing
          unequal parameter first second
      · exact False.elim (unequal rfl)
  | hmul left right leftInvariant rightInvariant =>
      intro first second
      rw [map_mul, coframeTwoFormLinear_mul]
      change coframeTwoFormMetricPairing 1
          (coframeTwoFormLinear (spinLorentzMatrix left)
            (coframeTwoFormLinear (spinLorentzMatrix right) first))
          (coframeTwoFormLinear (spinLorentzMatrix left)
            (coframeTwoFormLinear (spinLorentzMatrix right) second)) =
        coframeTwoFormMetricPairing 1 first second
      rw [leftInvariant, rightInvariant]

/-- Left Spin transport of the coframe leaves the generated spacetime
two-form metric pairing unchanged. -/
theorem coframeTwoFormMetricPairing_spin_coframe_invariant
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe)
    (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing
        (spinLorentzCoframeRepresentation groupElement coframe) first second =
      coframeTwoFormMetricPairing coframe first second := by
  change coframeTwoFormMetricPairing
      (spinLorentzMatrix groupElement * coframe) first second =
    coframeTwoFormMetricPairing coframe first second
  unfold coframeTwoFormMetricPairing
  rw [coframeTwoFormLinear_mul]
  simpa [coframeTwoFormMetricPairing, coframeTwoFormLinear_one,
    spinLorentzTwoFormRepresentation, spinLorentzTwoFormLinearEquiv,
    spinLorentzTwoFormLinearMap] using
    spinLorentzTwoForm_pairing_invariant groupElement
      (coframeTwoFormLinear coframe first)
      (coframeTwoFormLinear coframe second)

/-- On the nondegenerate branch, a Spin rotation of the internal coframe
leaves the dynamically generated spacetime Hodge operator unchanged. -/
theorem coframeGaugeSpacetimeHodgeLinear_spin_invariant
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeGaugeSpacetimeHodgeLinear
        (spinLorentzCoframeRepresentation groupElement coframe) =
      coframeGaugeSpacetimeHodgeLinear coframe := by
  apply LinearMap.ext
  intro form
  have transformedNondegenerate :
      Matrix.det
        (spinLorentzCoframeRepresentation groupElement coframe) ≠ 0 := by
    rw [spinLorentzCoframe_det]
    exact nondegenerate
  apply coframeTwoFormLinear_injective
    (spinLorentzCoframeRepresentation groupElement coframe)
    transformedNondegenerate
  rw [coframeTwoFormLinear_dynamicHodge
      (spinLorentzCoframeRepresentation groupElement coframe)
      transformedNondegenerate]
  symm
  change coframeTwoFormLinear (spinLorentzMatrix groupElement * coframe)
      (coframeGaugeSpacetimeHodgeLinear coframe form) =
    lorentzianCoframeHodge
      (coframeTwoFormLinear (spinLorentzMatrix groupElement * coframe) form)
  rw [coframeTwoFormLinear_mul]
  change coframeTwoFormLinear (spinLorentzMatrix groupElement)
      (coframeTwoFormLinear coframe
        (coframeGaugeSpacetimeHodgeLinear coframe form)) =
    lorentzianCoframeHodge
      (coframeTwoFormLinear (spinLorentzMatrix groupElement)
        (coframeTwoFormLinear coframe form))
  rw [coframeTwoFormLinear_dynamicHodge coframe nondegenerate]
  simpa [spinLorentzTwoFormRepresentation,
    spinLorentzTwoFormLinearEquiv, spinLorentzTwoFormLinearMap] using
    spinLorentzTwoForm_hodge_commute groupElement
      (coframeTwoFormLinear coframe form)

private theorem spinLorentzPhysicalBivector_row
    (groupElement : SpinPlus13) (bivector : PhysicalBivector)
    (internalPair : Fin 6) :
    spinLorentzPhysicalBivectorRepresentation groupElement bivector
        internalPair =
      ∑ sourceInternalPair : Fin 6,
        coframeWedge (spinLorentzMatrix groupElement)
            internalPair sourceInternalPair •
          bivector sourceInternalPair := by
  funext spacetimePair
  change spinLorentzPhysicalBivectorLinearEquiv groupElement bivector
      internalPair spacetimePair = _
  rw [spinLorentzPhysicalBivectorLinearEquiv_apply]
  rfl

/-- A spacetime linear operator commutes with the Spin action on the distinct
internal pair index of a physical bivector. -/
theorem physicalBivector_spacetimeLinearMap_spin_commute
    (groupElement : SpinPlus13)
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (bivector : PhysicalBivector) :
    (fun internalPair =>
      operator
        (spinLorentzPhysicalBivectorRepresentation groupElement bivector
          internalPair)) =
      spinLorentzPhysicalBivectorRepresentation groupElement
        (fun internalPair => operator (bivector internalPair)) := by
  funext internalPair
  rw [spinLorentzPhysicalBivector_row,
    spinLorentzPhysicalBivector_row]
  simp only [map_sum, LinearMap.map_smul]

/-- The generated spacetime Hodge is jointly equivariant under coframe and
physical-bivector Spin transport. -/
theorem gravitySpacetimeHodge_spin_covariant
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (bivector : PhysicalBivector) :
    gravitySpacetimeHodge
        (spinLorentzCoframeRepresentation groupElement coframe)
        (spinLorentzPhysicalBivectorRepresentation groupElement bivector) =
      spinLorentzPhysicalBivectorRepresentation groupElement
        (gravitySpacetimeHodge coframe bivector) := by
  unfold gravitySpacetimeHodge
  rw [coframeGaugeSpacetimeHodgeLinear_spin_invariant
    groupElement coframe nondegenerate]
  exact physicalBivector_spacetimeLinearMap_spin_commute groupElement
    (coframeGaugeSpacetimeHodgeLinear coframe) bivector

private theorem spinLorentzTwoForm_coefficient_orthogonality
    (groupElement : SpinPlus13) (first second : Fin 6) :
    (∑ target : Fin 6,
      lorentzianTwoFormSign target *
        coframeWedge (spinLorentzMatrix groupElement) target first *
        coframeWedge (spinLorentzMatrix groupElement) target second) =
      if first = second then lorentzianTwoFormSign first else 0 := by
  have invariant :
      coframeTwoFormMetricPairing 1
          (coframeTwoFormLinear (spinLorentzMatrix groupElement)
            (gaugeTwoFormCoordinate first))
          (coframeTwoFormLinear (spinLorentzMatrix groupElement)
            (gaugeTwoFormCoordinate second)) =
        coframeTwoFormMetricPairing 1
          (gaugeTwoFormCoordinate first)
          (gaugeTwoFormCoordinate second) := by
    simpa [spinLorentzTwoFormRepresentation,
      spinLorentzTwoFormLinearEquiv, spinLorentzTwoFormLinearMap] using
      spinLorentzTwoForm_pairing_invariant groupElement
        (gaugeTwoFormCoordinate first) (gaugeTwoFormCoordinate second)
  unfold coframeTwoFormMetricPairing at invariant
  simp only [coframeTwoFormLinear_one, LinearMap.id_apply] at invariant
  simp_rw [coframeTwoFormLinear_coordinate] at invariant
  by_cases equal : first = second
  · subst second
    simpa [gaugeTwoFormCoordinate] using invariant
  · have reverse : second ≠ first := Ne.symm equal
    simpa [gaugeTwoFormCoordinate, equal, reverse] using invariant

private theorem coframeTwoFormMetricPairing_sum_left
    (coframe : LorentzianCoframe) (coefficient : Fin 6 → ℝ)
    (forms : Fin 6 → GaugeTwoForm) (residual : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe
        (∑ pair : Fin 6, coefficient pair • forms pair) residual =
      ∑ pair : Fin 6,
        coefficient pair *
          coframeTwoFormMetricPairing coframe (forms pair) residual := by
  unfold coframeTwoFormMetricPairing
  simp only [map_sum, LinearMap.map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pair _
  apply Finset.sum_congr rfl
  intro sourcePair _
  ring

private theorem coframeTwoFormMetricPairing_sum_right
    (coframe : LorentzianCoframe) (coefficient : Fin 6 → ℝ)
    (forms : Fin 6 → GaugeTwoForm) (residual : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe residual
        (∑ pair : Fin 6, coefficient pair • forms pair) =
      ∑ pair : Fin 6,
        coefficient pair *
          coframeTwoFormMetricPairing coframe residual (forms pair) := by
  rw [coframeTwoFormMetricPairing_symmetric]
  simp_rw [coframeTwoFormMetricPairing_sum_left]
  apply Finset.sum_congr rfl
  intro pair _
  rw [coframeTwoFormMetricPairing_symmetric]

/-- Spin transport on the internal pair index preserves the physical
bivector pairing for every fixed dynamical coframe. -/
theorem gravityCoframePairing_internal_spin_invariant
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    gravityCoframePairing coframe
        (spinLorentzPhysicalBivectorRepresentation groupElement first)
        (spinLorentzPhysicalBivectorRepresentation groupElement second) =
      gravityCoframePairing coframe first second := by
  unfold gravityCoframePairing
  simp_rw [spinLorentzPhysicalBivector_row,
    coframeTwoFormMetricPairing_sum_left,
    coframeTwoFormMetricPairing_sum_right]
  calc
    ∑ internalPair : Fin 6,
        lorentzianTwoFormSign internalPair *
          ∑ firstPair : Fin 6,
            coframeWedge (spinLorentzMatrix groupElement)
                internalPair firstPair *
              ∑ secondPair : Fin 6,
                coframeWedge (spinLorentzMatrix groupElement)
                    internalPair secondPair *
                  coframeTwoFormMetricPairing coframe
                    (first firstPair) (second secondPair) =
      ∑ firstPair : Fin 6, ∑ secondPair : Fin 6,
        (∑ internalPair : Fin 6,
          lorentzianTwoFormSign internalPair *
            coframeWedge (spinLorentzMatrix groupElement)
              internalPair firstPair *
            coframeWedge (spinLorentzMatrix groupElement)
              internalPair secondPair) *
          coframeTwoFormMetricPairing coframe
            (first firstPair) (second secondPair) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro firstPair _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro secondPair _
      apply Finset.sum_congr rfl
      intro internalPair _
      ring
    _ = ∑ firstPair : Fin 6, ∑ secondPair : Fin 6,
        (if firstPair = secondPair
          then lorentzianTwoFormSign firstPair else 0) *
          coframeTwoFormMetricPairing coframe
            (first firstPair) (second secondPair) := by
      simp_rw [spinLorentzTwoForm_coefficient_orthogonality]
    _ = ∑ internalPair : Fin 6,
        lorentzianTwoFormSign internalPair *
          coframeTwoFormMetricPairing coframe
            (first internalPair) (second internalPair) := by
      simp

private theorem gravityCoframePairing_spin_coframe_invariant
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    gravityCoframePairing
        (spinLorentzCoframeRepresentation groupElement coframe)
        first second =
      gravityCoframePairing coframe first second := by
  unfold gravityCoframePairing
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [coframeTwoFormMetricPairing_spin_coframe_invariant]

/-- The dynamical physical-bivector pairing is jointly invariant when the
coframe and both bivectors follow their actual Spin representations. -/
theorem gravityCoframePairing_spin_invariant
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    gravityCoframePairing
        (spinLorentzCoframeRepresentation groupElement coframe)
        (spinLorentzPhysicalBivectorRepresentation groupElement first)
        (spinLorentzPhysicalBivectorRepresentation groupElement second) =
      gravityCoframePairing coframe first second := by
  rw [gravityCoframePairing_spin_coframe_invariant]
  exact gravityCoframePairing_internal_spin_invariant
    groupElement coframe first second

/-! ## Candidate-A gravity point field and densities -/

/-- Fiberwise gravity-sector Spin transport.  Non-gravity fields are retained
verbatim, so this is deliberately not a full unified local-gauge action. -/
def transformResidualLinearGravityPointField
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    StageNineContinuumPointField :=
  { field with
      coframe := spinLorentzCoframeRepresentation groupElement field.coframe
      gravityCurvature :=
        spinLorentzPhysicalBivectorRepresentation groupElement
          field.gravityCurvature
      gravityAuxiliary :=
        spinLorentzPhysicalBivectorRepresentation groupElement
          field.gravityAuxiliary
      gravitySimplicityMultiplier :=
        spinLorentzPhysicalBivectorRepresentation groupElement
          field.gravitySimplicityMultiplier }

@[simp] theorem transformResidualLinearGravityPointField_coframe
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    (transformResidualLinearGravityPointField groupElement field).coframe =
      spinLorentzCoframeRepresentation groupElement field.coframe :=
  rfl

/-- The candidate-A fiberwise gravity transport preserves the dynamical
volume density. -/
theorem generatedVolumeDensity_spin_invariant
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    generatedVolumeDensity
        (transformResidualLinearGravityPointField groupElement field) =
      generatedVolumeDensity field := by
  unfold generatedVolumeDensity
  rw [transformResidualLinearGravityPointField_coframe,
    spinLorentzCoframe_det]

/-- The actual residual `B - II+(e)` transports faithfully under the same
physical-bivector action. -/
theorem generatedGravitySimplicityResidual_spin_covariant
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    generatedGravitySimplicityResidual
        (transformResidualLinearGravityPointField groupElement field) =
      spinLorentzPhysicalBivectorRepresentation groupElement
        (generatedGravitySimplicityResidual field) := by
  unfold generatedGravitySimplicityResidual
  simp only [transformResidualLinearGravityPointField]
  rw [physicalIIPlusBivector_spin_covariant, map_sub]

/-- Spin transport preserves and reflects the selected simplicity zero fiber.
The conclusion follows from the generated covariance law and the existing
linear equivalence; no shell-membership certificate is supplied. -/
theorem generatedGravitySimplicityResidual_spin_eq_zero_iff
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    generatedGravitySimplicityResidual
          (transformResidualLinearGravityPointField groupElement field) = 0 ↔
      generatedGravitySimplicityResidual field = 0 := by
  rw [generatedGravitySimplicityResidual_spin_covariant]
  constructor
  · intro transportedZero
    apply (spinLorentzPhysicalBivectorRepresentation groupElement).injective
    simpa using transportedZero
  · rintro residualZero
    rw [residualZero]
    exact map_zero _

/-- The same faithful transport preserves and reflects a nonzero routing
obstruction. -/
theorem generatedGravitySimplicityResidual_spin_ne_zero_iff
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField) :
    generatedGravitySimplicityResidual
          (transformResidualLinearGravityPointField groupElement field) ≠ 0 ↔
      generatedGravitySimplicityResidual field ≠ 0 := by
  exact not_congr
    (generatedGravitySimplicityResidual_spin_eq_zero_iff groupElement field)

/-- On the nondegenerate branch, the residual-linear simplicity density is
fiberwise Spin invariant. -/
theorem generatedGravityResidualLinearSimplicityDensity_spin_invariant
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    generatedGravityResidualLinearSimplicityDensity
        (transformResidualLinearGravityPointField groupElement field) =
      generatedGravityResidualLinearSimplicityDensity field := by
  unfold generatedGravityResidualLinearSimplicityDensity
  change gravityCoframePairing
      (spinLorentzCoframeRepresentation groupElement field.coframe)
      (spinLorentzPhysicalBivectorRepresentation groupElement
        field.gravitySimplicityMultiplier)
      (gravitySpacetimeHodge
        (spinLorentzCoframeRepresentation groupElement field.coframe)
        (generatedGravitySimplicityResidual
          (transformResidualLinearGravityPointField groupElement field))) =
    gravityCoframePairing field.coframe field.gravitySimplicityMultiplier
      (gravitySpacetimeHodge field.coframe
        (generatedGravitySimplicityResidual field))
  rw [generatedGravitySimplicityResidual_spin_covariant]
  rw [gravitySpacetimeHodge_spin_covariant
    groupElement field.coframe nondegenerate]
  exact gravityCoframePairing_spin_invariant groupElement field.coframe
    field.gravitySimplicityMultiplier
    (gravitySpacetimeHodge field.coframe
      (generatedGravitySimplicityResidual field))

/-- On the nondegenerate branch, the BF/constitutive gravity density is
fiberwise Spin invariant when `F`, `B`, and `e` follow the same action. -/
theorem generatedGravityBFDensity_spin_invariant
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    generatedGravityBFDensity
        (transformResidualLinearGravityPointField groupElement field) =
      generatedGravityBFDensity field := by
  unfold generatedGravityBFDensity
  change gravityCoframePairing
        (spinLorentzCoframeRepresentation groupElement field.coframe)
        (spinLorentzPhysicalBivectorRepresentation groupElement
          field.gravityAuxiliary)
        (gravitySpacetimeHodge
          (spinLorentzCoframeRepresentation groupElement field.coframe)
          (spinLorentzPhysicalBivectorRepresentation groupElement
            field.gravityCurvature)) -
      (1 / 2 : ℝ) *
        gravityCoframePairing
          (spinLorentzCoframeRepresentation groupElement field.coframe)
          (spinLorentzPhysicalBivectorRepresentation groupElement
            field.gravityAuxiliary)
          (gravitySpacetimeHodge
            (spinLorentzCoframeRepresentation groupElement field.coframe)
            (gravityInternalDualEquiv
              (spinLorentzPhysicalBivectorRepresentation groupElement
                field.gravityAuxiliary))) =
    gravityCoframePairing field.coframe field.gravityAuxiliary
        (gravitySpacetimeHodge field.coframe field.gravityCurvature) -
      (1 / 2 : ℝ) *
        gravityCoframePairing field.coframe field.gravityAuxiliary
          (gravitySpacetimeHodge field.coframe
            (gravityInternalDualEquiv field.gravityAuxiliary))
  rw [gravitySpacetimeHodge_spin_covariant
    groupElement field.coframe nondegenerate]
  rw [gravityInternalDualEquiv_spin_commute]
  rw [gravitySpacetimeHodge_spin_covariant
    groupElement field.coframe nondegenerate]
  rw [gravityCoframePairing_spin_invariant,
    gravityCoframePairing_spin_invariant]

/-- The extracted candidate-A gravity fiber density: volume times the sum of
the residual-linear simplicity and BF terms. -/
def generatedResidualLinearGravityFiberDensity
    (field : StageNineContinuumPointField) : ℝ :=
  generatedVolumeDensity field *
    (generatedGravityResidualLinearSimplicityDensity field +
      generatedGravityBFDensity field)

/-- Exact jurisdiction seam: the fiber density above is the complete gravity
summand of candidate A, while the non-gravity core remains a separate term.
In particular, the gravity invariance theorem below is not a theorem about
the full unified local density. -/
theorem generatedResidualLinearUnifiedLocalDensityAtBoundary_eq_gravityFiber_add_nonGravity
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedResidualLinearUnifiedLocalDensityAtBoundary source boundary
        chart point field =
      generatedResidualLinearGravityFiberDensity field +
        generatedVolumeDensity field *
          generatedUnifiedLocalDensityNonGravityCoreAtBoundary
            source boundary chart point field := by
  unfold generatedResidualLinearUnifiedLocalDensityAtBoundary
    generatedUnifiedLocalDensityCoreAtBoundary
    generatedResidualLinearGravityFiberDensity
  ring

/-- The complete candidate-A gravity fiber density is Spin invariant on the
nondegenerate branch.  This does not cover the untouched matter/gauge fields
or holonomic local connection transformation. -/
theorem generatedResidualLinearGravityFiberDensity_spin_invariant
    (groupElement : SpinPlus13) (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    generatedResidualLinearGravityFiberDensity
        (transformResidualLinearGravityPointField groupElement field) =
      generatedResidualLinearGravityFiberDensity field := by
  unfold generatedResidualLinearGravityFiberDensity
  rw [generatedVolumeDensity_spin_invariant,
    generatedGravityResidualLinearSimplicityDensity_spin_invariant
      groupElement field nondegenerate,
    generatedGravityBFDensity_spin_invariant
      groupElement field nondegenerate]

end

end
  SaturationMonoid.PhysicsCore.StageNineResidualLinearPlebanskiFiberwiseSpinCovariance
