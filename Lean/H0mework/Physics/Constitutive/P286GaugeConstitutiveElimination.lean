import H0mework.Physics.Gauge.GaugeAuxiliaryVariation
import H0mework.Physics.GaugeAction.P286GaugeAuxiliaryVariation

/-!
# Form-native three-block P286 constitutive elimination

This module inverts the exact three-coupling constitutive operator generated
by the authoritative form-native action.  The same live coframe Hodge is used
in all three blocks, while the source-owned strong, weak, and hypercharge
units are inverted independently.

The eliminated auxiliary is a deterministic readout

```text
B_elim = -diag(g_s^-2, g_w^-2, g_y^-2) (*_e F).
```

The Lorentzian minus sign is derived from `*_e^2 = -1`.  No auxiliary
solution, inverse witness, equation receipt, branch selector, target field,
or additional coupling is supplied.  This is conditional algebraic recovery;
it does not generate the connection Euler equation or a stationary actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeConstitutiveElimination

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Dependency-light lifted Hodge algebra -/

def formNativeP286BlockScale
    (strong weak hypercharge : ℝ)
    (form : FormNativeP286GaugeTwoForm) : FormNativeP286GaugeTwoForm :=
  fun pair =>
    (strong • (form pair).1,
      weak • (form pair).2.1,
      hypercharge • (form pair).2.2)

def formNativeP286LiftedCoframeHodge
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeTwoForm) : FormNativeP286GaugeTwoForm :=
  liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear coframe) form

private theorem liftGaugeTwoFormOperator_smul_operator_local
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (parameter : ℝ) (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : Fin 6 → V) :
    liftGaugeTwoFormOperator (parameter • operator) form =
      parameter • liftGaugeTwoFormOperator operator form := by
  funext output
  unfold liftGaugeTwoFormOperator gaugeOperatorCoefficient
  simp only [Pi.smul_apply, LinearMap.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  change
    (parameter *
        operator (fun candidate => if candidate = input then 1 else 0)
          output) • form input =
      parameter •
        (operator (fun candidate => if candidate = input then 1 else 0)
          output • form input)
  rw [mul_smul]

private theorem liftGaugeTwoFormOperator_smul_form_local
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (parameter : ℝ) (form : Fin 6 → V) :
    liftGaugeTwoFormOperator operator (parameter • form) =
      parameter • liftGaugeTwoFormOperator operator form := by
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  simp only [smul_smul]
  rw [mul_comm]

private theorem formNativeP286LiftedCoframeHodge_neg
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeTwoForm) :
    formNativeP286LiftedCoframeHodge coframe (-form) =
      -formNativeP286LiftedCoframeHodge coframe form := by
  unfold formNativeP286LiftedCoframeHodge
  rw [← neg_one_smul ℝ form]
  rw [liftGaugeTwoFormOperator_smul_form_local]
  exact neg_one_smul ℝ
    (liftGaugeTwoFormOperator
      (coframeGaugeSpacetimeHodgeLinear coframe) form)

@[simp] theorem formNativeP286LiftedCoframeHodge_zero
    (coframe : LorentzianCoframe) :
    formNativeP286LiftedCoframeHodge coframe 0 = 0 := by
  funext output
  simp [formNativeP286LiftedCoframeHodge, liftGaugeTwoFormOperator]

@[simp] theorem formNativeP286BlockScale_zero
    (strong weak hypercharge : ℝ) :
    formNativeP286BlockScale strong weak hypercharge 0 = 0 := by
  funext pair
  simp [formNativeP286BlockScale]

theorem formNativeP286LiftedCoframeHodge_square
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (form : FormNativeP286GaugeTwoForm) :
    formNativeP286LiftedCoframeHodge coframe
        (formNativeP286LiftedCoframeHodge coframe form) =
      -form := by
  funext output
  apply p286CoordinateEquiv.injective
  have coordinateSquare := congrFun
    (liftGaugeTwoFormOperator_coframeHodge_square_p286 coframe nondegenerate
      (fun pair => p286CoordinateEquiv (form pair))) output
  simpa [formNativeP286LiftedCoframeHodge,
    p286CoordinateEquiv_liftGaugeTwoFormOperator] using coordinateSquare

theorem formNativeP286LiftedCoframeHodge_blockScale
    (coframe : LorentzianCoframe)
    (strong weak hypercharge : ℝ)
    (form : FormNativeP286GaugeTwoForm) :
    formNativeP286LiftedCoframeHodge coframe
        (formNativeP286BlockScale strong weak hypercharge form) =
      formNativeP286BlockScale strong weak hypercharge
        (formNativeP286LiftedCoframeHodge coframe form) := by
  funext output
  apply Prod.ext
  · change
      liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear coframe)
          (strong • fun input => (form input).1) output =
        strong •
          (liftGaugeTwoFormOperator
            (coframeGaugeSpacetimeHodgeLinear coframe) form output).1
    rw [liftGaugeTwoFormOperator_smul_form_local]
    rw [liftGaugeTwoFormOperator_p286_strong]
    rfl
  · apply Prod.ext
    · change
        liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear coframe)
            (weak • fun input => (form input).2.1) output =
          weak •
            (liftGaugeTwoFormOperator
              (coframeGaugeSpacetimeHodgeLinear coframe) form output).2.1
      rw [liftGaugeTwoFormOperator_smul_form_local]
      rw [liftGaugeTwoFormOperator_p286_weak]
      rfl
    · change
        liftGaugeTwoFormOperator (coframeGaugeSpacetimeHodgeLinear coframe)
            (hypercharge • fun input => (form input).2.2) output =
          hypercharge •
            (liftGaugeTwoFormOperator
              (coframeGaugeSpacetimeHodgeLinear coframe) form output).2.2
      rw [liftGaugeTwoFormOperator_smul_form_local]
      rw [liftGaugeTwoFormOperator_p286_hypercharge]
      rfl

theorem formNativeP286BlockwiseConstitutive_eq_blockScale_hodge
    (coframe : LorentzianCoframe)
    (strong weak hypercharge : ℝ)
    (form : FormNativeP286GaugeTwoForm) :
    formNativeP286BlockwiseConstitutive coframe strong weak hypercharge form =
      formNativeP286BlockScale strong weak hypercharge
        (formNativeP286LiftedCoframeHodge coframe form) := by
  funext output
  apply Prod.ext
  · change
      liftGaugeTwoFormOperator
          (strong • coframeGaugeSpacetimeHodgeLinear coframe)
          (fun input => (form input).1) output =
        strong •
          (liftGaugeTwoFormOperator
            (coframeGaugeSpacetimeHodgeLinear coframe) form output).1
    rw [liftGaugeTwoFormOperator_smul_operator_local]
    rw [liftGaugeTwoFormOperator_p286_strong]
    rfl
  · apply Prod.ext
    · change
        liftGaugeTwoFormOperator
            (weak • coframeGaugeSpacetimeHodgeLinear coframe)
            (fun input => (form input).2.1) output =
          weak •
            (liftGaugeTwoFormOperator
              (coframeGaugeSpacetimeHodgeLinear coframe) form output).2.1
      rw [liftGaugeTwoFormOperator_smul_operator_local]
      rw [liftGaugeTwoFormOperator_p286_weak]
      rfl
    · change
        liftGaugeTwoFormOperator
            (hypercharge • coframeGaugeSpacetimeHodgeLinear coframe)
            (fun input => (form input).2.2) output =
          hypercharge •
            (liftGaugeTwoFormOperator
              (coframeGaugeSpacetimeHodgeLinear coframe) form output).2.2
      rw [liftGaugeTwoFormOperator_smul_operator_local]
      rw [liftGaugeTwoFormOperator_p286_hypercharge]
      rfl

/-! ## Three-block inverse and exact zero fiber -/

/-- Unique inverse-constitutive image selected by the live coframe and the
three source-boundary coupling units. -/
def formNativeP286GaugeEliminatedAuxiliaryAtBoundary
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (curvature : FormNativeP286GaugeTwoForm) :
    FormNativeP286GaugeTwoForm :=
  -formNativeP286BlockScale
    ((boundary.strongCouplingSquared : ℝ)⁻¹)
    ((boundary.weakCouplingSquared : ℝ)⁻¹)
    ((boundary.hyperchargeCouplingSquared : ℝ)⁻¹)
    (formNativeP286LiftedCoframeHodge coframe curvature)

theorem formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature : FormNativeP286GaugeTwoForm) :
    formNativeP286BlockwiseConstitutive coframe
        (boundary.strongCouplingSquared : ℝ)
        (boundary.weakCouplingSquared : ℝ)
        (boundary.hyperchargeCouplingSquared : ℝ)
        (formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe
          curvature) =
      curvature := by
  rw [formNativeP286BlockwiseConstitutive_eq_blockScale_hodge]
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary
  rw [formNativeP286LiftedCoframeHodge_neg]
  rw [formNativeP286LiftedCoframeHodge_blockScale]
  rw [formNativeP286LiftedCoframeHodge_square coframe nondegenerate]
  funext pair
  apply Prod.ext
  · simp only [formNativeP286BlockScale, Pi.neg_apply, Prod.fst_neg,
      smul_neg, neg_neg, smul_smul]
    rw [mul_inv_cancel₀ (Units.ne_zero boundary.strongCouplingSquared)]
    simp
  · apply Prod.ext
    · simp only [formNativeP286BlockScale, Pi.neg_apply, Prod.snd_neg,
        Prod.fst_neg, smul_neg, neg_neg, smul_smul]
      rw [mul_inv_cancel₀ (Units.ne_zero boundary.weakCouplingSquared)]
      simp
    · simp only [formNativeP286BlockScale, Pi.neg_apply, Prod.snd_neg,
        smul_neg, neg_neg, smul_smul]
      rw [mul_inv_cancel₀ (Units.ne_zero boundary.hyperchargeCouplingSquared)]
      simp

theorem formNativeP286GaugeEliminatedAuxiliaryAtBoundary_constitutive
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (auxiliary : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe
        (formNativeP286BlockwiseConstitutive coframe
          (boundary.strongCouplingSquared : ℝ)
          (boundary.weakCouplingSquared : ℝ)
          (boundary.hyperchargeCouplingSquared : ℝ) auxiliary) =
      auxiliary := by
  unfold formNativeP286GaugeEliminatedAuxiliaryAtBoundary
  rw [formNativeP286BlockwiseConstitutive_eq_blockScale_hodge]
  rw [formNativeP286LiftedCoframeHodge_blockScale]
  rw [formNativeP286LiftedCoframeHodge_square coframe nondegenerate]
  funext pair
  apply Prod.ext
  · simp only [formNativeP286BlockScale, Pi.neg_apply, Prod.fst_neg,
      smul_neg, neg_neg, smul_smul]
    rw [inv_mul_cancel₀ (Units.ne_zero boundary.strongCouplingSquared)]
    simp
  · apply Prod.ext
    · simp only [formNativeP286BlockScale, Pi.neg_apply, Prod.snd_neg,
        Prod.fst_neg, smul_neg, neg_neg, smul_smul]
      rw [inv_mul_cancel₀ (Units.ne_zero boundary.weakCouplingSquared)]
      simp
    · simp only [formNativeP286BlockScale, Pi.neg_apply, Prod.snd_neg,
        smul_neg, neg_neg, smul_smul]
      rw [inv_mul_cancel₀ (Units.ne_zero boundary.hyperchargeCouplingSquared)]
      simp

theorem formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary boundary field ↔
      field.gaugeAuxiliary =
        formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary field.coframe
          field.gaugeCurvature := by
  constructor
  · intro equation
    unfold FormNativeP286GaugeAuxiliaryEquationAtBoundary at equation
    have transformed := congrArg
      (formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary field.coframe)
      equation
    rw [formNativeP286GaugeEliminatedAuxiliaryAtBoundary_constitutive boundary
      field.coframe nondegenerate field.gaugeAuxiliary] at transformed
    exact transformed.symm
  · intro auxiliaryEquality
    unfold FormNativeP286GaugeAuxiliaryEquationAtBoundary
    rw [auxiliaryEquality]
    exact formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves boundary
      field.coframe nondegenerate field.gaugeCurvature |>.symm

theorem formNativeP286GaugeEliminatedAuxiliaryAtBoundary_eq_zero_iff
    (boundary : EmpiricalReferenceScaleCouplings)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature : FormNativeP286GaugeTwoForm) :
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary boundary coframe
        curvature = 0 ↔
      curvature = 0 := by
  constructor
  · intro auxiliaryZero
    have solved := formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves
      boundary coframe nondegenerate curvature
    rw [auxiliaryZero] at solved
    have constitutiveZero :
        formNativeP286BlockwiseConstitutive coframe
          (boundary.strongCouplingSquared : ℝ)
          (boundary.weakCouplingSquared : ℝ)
          (boundary.hyperchargeCouplingSquared : ℝ) 0 = 0 := by
      rw [formNativeP286BlockwiseConstitutive_eq_blockScale_hodge]
      simp
    rw [constitutiveZero] at solved
    exact solved.symm
  · rintro rfl
    simp [formNativeP286GaugeEliminatedAuxiliaryAtBoundary]

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeConstitutiveElimination
