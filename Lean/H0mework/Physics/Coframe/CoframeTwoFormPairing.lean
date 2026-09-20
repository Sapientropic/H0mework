import H0mework.Physics.Exterior.GlobalIntegratedAction

namespace SaturationMonoid.PhysicsCore.StageNineCoframeTwoFormPairing

open ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction
open StageNineBlockwiseConstitutive
open EmpiricalReferenceScaleCouplingBoundary

noncomputable section

@[simp] theorem internalBivectorDual_component_zero
    (bivector : PhysicalBivector) :
    internalBivectorDual bivector 0 = bivector 3 := by
  rfl

@[simp] theorem internalBivectorDual_component_one
    (bivector : PhysicalBivector) :
    internalBivectorDual bivector 1 = bivector 4 := by
  rfl

@[simp] theorem internalBivectorDual_component_two
    (bivector : PhysicalBivector) :
    internalBivectorDual bivector 2 = bivector 5 := by
  rfl

@[simp] theorem internalBivectorDual_component_three
    (bivector : PhysicalBivector) :
    internalBivectorDual bivector 3 = -bivector 0 := by
  rfl

@[simp] theorem internalBivectorDual_component_four
    (bivector : PhysicalBivector) :
    internalBivectorDual bivector 4 = -bivector 1 := by
  rfl

@[simp] theorem internalBivectorDual_component_five
    (bivector : PhysicalBivector) :
    internalBivectorDual bivector 5 = -bivector 2 := by
  rfl

theorem coframeTwoFormLinear_one :
    coframeTwoFormLinear (1 : LorentzianCoframe) = LinearMap.id := by
  apply LinearMap.ext
  intro form
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, coframeWedge, pairFirst, pairSecond,
      Matrix.one_apply, Fin.sum_univ_six]

/-- At the identity coframe the dynamical gravity pairing is exactly the
fixed signed coordinate pairing.  This normalization fact belongs to the
coframe/pairing layer; it must not be recovered by importing a fixed-source
or fixed-actual module. -/
theorem gravityCoframePairing_one_eq_coordinate
    (first second : PhysicalBivector) :
    gravityCoframePairing (1 : LorentzianCoframe) first second =
      gravityCoordinatePairing first second := by
  unfold gravityCoframePairing coframeTwoFormMetricPairing
    gravityCoordinatePairing
  simp_rw [coframeTwoFormLinear_one]
  apply Finset.sum_congr rfl
  intro internalPair _
  simp only [LinearMap.id_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spacetimePair _
  ring

/-- At the identity coframe the dynamical spacetime Hodge is the fixed
Lorentzian two-form Hodge on every internal bivector coordinate. -/
theorem gravitySpacetimeHodge_one_eq_fixed
    (bivector : PhysicalBivector) :
    gravitySpacetimeHodge (1 : LorentzianCoframe) bivector =
      fun internalPair => lorentzianCoframeHodge (bivector internalPair) := by
  unfold gravitySpacetimeHodge
  rw [coframeGaugeSpacetimeHodgeLinear,
    inverseCoframeTwoFormLinear, inv_one,
    coframeTwoFormLinear_one]
  rfl

theorem coframeTwoFormLinear_mul
    (first second : LorentzianCoframe) :
    coframeTwoFormLinear (first * second) =
      (coframeTwoFormLinear first).comp (coframeTwoFormLinear second) := by
  apply LinearMap.ext
  intro form
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, coframeWedge, pairFirst, pairSecond,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six]
  all_goals ring

theorem coframeTwoFormLinear_inv_comp
    (coframe : LorentzianCoframe) (nondegenerate : Matrix.det coframe ≠ 0) :
    (coframeTwoFormLinear coframe⁻¹).comp
        (coframeTwoFormLinear coframe) = LinearMap.id := by
  rw [← coframeTwoFormLinear_mul,
    Matrix.nonsing_inv_mul coframe (isUnit_iff_ne_zero.mpr nondegenerate),
    coframeTwoFormLinear_one]

theorem coframeTwoFormLinear_comp_inv
    (coframe : LorentzianCoframe) (nondegenerate : Matrix.det coframe ≠ 0) :
    (coframeTwoFormLinear coframe).comp
        (coframeTwoFormLinear coframe⁻¹) = LinearMap.id := by
  rw [← coframeTwoFormLinear_mul,
    Matrix.mul_nonsing_inv coframe (isUnit_iff_ne_zero.mpr nondegenerate),
    coframeTwoFormLinear_one]

theorem coframeTwoFormLinear_injective
    (coframe : LorentzianCoframe) (nondegenerate : Matrix.det coframe ≠ 0) :
    Function.Injective (coframeTwoFormLinear coframe) := by
  intro first second equality
  have := congrArg (coframeTwoFormLinear coframe⁻¹) equality
  have cancellation := coframeTwoFormLinear_inv_comp coframe nondegenerate
  calc
    first = ((coframeTwoFormLinear coframe⁻¹).comp
        (coframeTwoFormLinear coframe)) first := by rw [cancellation]; rfl
    _ = ((coframeTwoFormLinear coframe⁻¹).comp
        (coframeTwoFormLinear coframe)) second := this
    _ = second := by rw [cancellation]; rfl

theorem coframeTwoFormLinear_dynamicHodge
    (coframe : LorentzianCoframe) (nondegenerate : Matrix.det coframe ≠ 0)
    (form : GaugeTwoForm) :
    coframeTwoFormLinear coframe
        (coframeGaugeSpacetimeHodgeLinear coframe form) =
      lorentzianCoframeHodge (coframeTwoFormLinear coframe form) := by
  have cancellation := congrArg
    (fun operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm =>
      operator (lorentzianCoframeHodge (coframeTwoFormLinear coframe form)))
    (coframeTwoFormLinear_comp_inv coframe nondegenerate)
  simpa [coframeGaugeSpacetimeHodgeLinear,
    inverseCoframeTwoFormLinear,
    lorentzianCoframeHodgeEquiv] using cancellation

theorem fixedLorentzTwoFormPairing_hodge_symmetric
    (first second : GaugeTwoForm) :
    (∑ pair : Fin 6,
      lorentzianTwoFormSign pair * first pair *
        lorentzianCoframeHodge second pair) =
    ∑ pair : Fin 6,
      lorentzianTwoFormSign pair *
        lorentzianCoframeHodge first pair * second pair := by
  simp [lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, lorentzianCoframeHodge, Fin.sum_univ_six]
  ring

/-- Legacy coordinate dot, retained only to state the negative regression
that forced the coframe-generated metric pairing above. -/
def rawTwoFormCoordinateDot
    (first second : GaugeTwoForm) : ℝ :=
  ∑ pair : Fin 6, first pair * second pair

theorem rawTwoFormCoordinateDot_hodge_skew
    (first second : GaugeTwoForm) :
    rawTwoFormCoordinateDot first (lorentzianCoframeHodge second) =
      -rawTwoFormCoordinateDot
        (lorentzianCoframeHodge first) second := by
  simp [rawTwoFormCoordinateDot, lorentzianCoframeHodge,
    Fin.sum_univ_six]
  ring

def timeSpaceCoordinateBasis : GaugeTwoForm :=
  fun pair => if pair = 0 then 1 else 0

def spatialCoordinateBasis : GaugeTwoForm :=
  fun pair => if pair = 3 then 1 else 0

/-- Negative regression: raw coordinate dot makes the fixed Lorentz Hodge
skew rather than self-adjoint.  Replacing the Cartan label or hand-filling a
sign table cannot repair this structural mismatch. -/
theorem rawTwoFormCoordinateDot_hodge_selfAdjoint_fake_rejected :
    rawTwoFormCoordinateDot spatialCoordinateBasis
        (lorentzianCoframeHodge timeSpaceCoordinateBasis) ≠
      rawTwoFormCoordinateDot
        (lorentzianCoframeHodge spatialCoordinateBasis)
        timeSpaceCoordinateBasis := by
  have rightValue :
      rawTwoFormCoordinateDot
          (lorentzianCoframeHodge spatialCoordinateBasis)
          timeSpaceCoordinateBasis = 1 := by
    norm_num [rawTwoFormCoordinateDot, timeSpaceCoordinateBasis,
      spatialCoordinateBasis, lorentzianCoframeHodge, Fin.sum_univ_six]
  have skew := rawTwoFormCoordinateDot_hodge_skew
    spatialCoordinateBasis timeSpaceCoordinateBasis
  rw [rightValue] at skew
  rw [rightValue]
  linarith

theorem coframeTwoFormMetricPairing_symmetric
    (coframe : LorentzianCoframe) (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe first second =
      coframeTwoFormMetricPairing coframe second first := by
  unfold coframeTwoFormMetricPairing
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem coframeTwoFormMetricPairing_hodge_symmetric
    (coframe : LorentzianCoframe) (nondegenerate : Matrix.det coframe ≠ 0)
    (first second : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe first
        (coframeGaugeSpacetimeHodgeLinear coframe second) =
      coframeTwoFormMetricPairing coframe
        (coframeGaugeSpacetimeHodgeLinear coframe first) second := by
  unfold coframeTwoFormMetricPairing
  simp_rw [coframeTwoFormLinear_dynamicHodge coframe nondegenerate]
  exact fixedLorentzTwoFormPairing_hodge_symmetric
    (coframeTwoFormLinear coframe first)
    (coframeTwoFormLinear coframe second)

theorem coframeGaugeSpacetimeHodgeLinear_square
    (coframe : LorentzianCoframe) (nondegenerate : Matrix.det coframe ≠ 0)
    (form : GaugeTwoForm) :
    coframeGaugeSpacetimeHodgeLinear coframe
        (coframeGaugeSpacetimeHodgeLinear coframe form) = -form := by
  apply coframeTwoFormLinear_injective coframe nondegenerate
  rw [coframeTwoFormLinear_dynamicHodge coframe nondegenerate,
    coframeTwoFormLinear_dynamicHodge coframe nondegenerate]
  have fixedSquare := congrArg
    (fun operator : LorentzianTwoFormHodgeOperator =>
      operator (coframeTwoFormLinear coframe form))
    lorentzianCoframeHodge_square
  simpa using fixedSquare

theorem gravityCoframePairing_symmetric
    (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    gravityCoframePairing coframe first second =
      gravityCoframePairing coframe second first := by
  unfold gravityCoframePairing
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [coframeTwoFormMetricPairing_symmetric]

theorem gravityCoframePairing_spacetimeHodge_symmetric
    (coframe : LorentzianCoframe) (nondegenerate : Matrix.det coframe ≠ 0)
    (first second : PhysicalBivector) :
    gravityCoframePairing coframe first
        (gravitySpacetimeHodge coframe second) =
      gravityCoframePairing coframe
        (gravitySpacetimeHodge coframe first) second := by
  unfold gravityCoframePairing gravitySpacetimeHodge
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [coframeTwoFormMetricPairing_hodge_symmetric coframe nondegenerate]

theorem gravityCoframePairing_internalDual_symmetric
    (coframe : LorentzianCoframe)
    (first second : PhysicalBivector) :
    gravityCoframePairing coframe first
        (gravityInternalDualEquiv second) =
      gravityCoframePairing coframe
        (gravityInternalDualEquiv first) second := by
  unfold gravityCoframePairing coframeTwoFormMetricPairing
  simp [gravityInternalDualEquiv, gravityInternalDualLinear,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Fin.sum_univ_six]
  ring

theorem gravitySpacetimeHodge_internalDual_commute
    (coframe : LorentzianCoframe) (bivector : PhysicalBivector) :
    gravitySpacetimeHodge coframe (gravityInternalDualEquiv bivector) =
      gravityInternalDualEquiv
        (gravitySpacetimeHodge coframe bivector) := by
  change gravitySpacetimeHodge coframe (internalBivectorDual bivector) =
    internalBivectorDual (gravitySpacetimeHodge coframe bivector)
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [gravitySpacetimeHodge, internalBivectorDual,
      lorentzianCoframeHodge]

theorem gravityConstitutiveBilinear_symmetric
    (coframe : LorentzianCoframe) (nondegenerate : Matrix.det coframe ≠ 0)
    (first second : PhysicalBivector) :
    gravityCoframePairing coframe first
        (gravitySpacetimeHodge coframe
          (gravityInternalDualEquiv second)) =
      gravityCoframePairing coframe second
        (gravitySpacetimeHodge coframe
          (gravityInternalDualEquiv first)) := by
  calc
    gravityCoframePairing coframe first
        (gravitySpacetimeHodge coframe
          (gravityInternalDualEquiv second)) =
      gravityCoframePairing coframe
        (gravitySpacetimeHodge coframe first)
        (gravityInternalDualEquiv second) :=
      gravityCoframePairing_spacetimeHodge_symmetric
        coframe nondegenerate first (gravityInternalDualEquiv second)
    _ = gravityCoframePairing coframe
        (gravityInternalDualEquiv
          (gravitySpacetimeHodge coframe first)) second :=
      gravityCoframePairing_internalDual_symmetric coframe
        (gravitySpacetimeHodge coframe first) second
    _ = gravityCoframePairing coframe
        (gravitySpacetimeHodge coframe
          (gravityInternalDualEquiv first)) second := by
      rw [gravitySpacetimeHodge_internalDual_commute]
    _ = gravityCoframePairing coframe second
        (gravitySpacetimeHodge coframe
          (gravityInternalDualEquiv first)) :=
      gravityCoframePairing_symmetric coframe _ _

end

end SaturationMonoid.PhysicsCore.StageNineCoframeTwoFormPairing
