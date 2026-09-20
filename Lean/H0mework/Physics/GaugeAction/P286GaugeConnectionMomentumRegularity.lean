import H0mework.Physics.GaugeAction.P286GaugeConnectionWeakEquation

/-!
# S9-C3a4a: smooth P286 connection BF momentum

The dynamic coframe determinant, adjugate, inverse, volume density, and Hodge
are proved smooth from the primitive holonomic configuration.  The BF
differential momentum is then rewritten through the same-coframe polynomial
intertwiner, so its smoothness is generated from the coframe and P286
auxiliary field rather than accepted as a regularity receipt.

This is the analytic input for the genuine compact-support integration by
parts in C3a4b.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionMomentumRegularity

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionActionVariation
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open EmpiricalReferenceScaleCouplingBoundary
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286GaugeConnectionActionVariation.p286CoordinateIndexFintype

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem holonomicCoframe_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ configuration.coframe := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  exact smooth.1 row column

theorem holonomicCoframe_det_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point => Matrix.det (configuration.coframe point) := by
  rw [show (fun point => Matrix.det (configuration.coframe point)) =
      fun point => ∑ σ : Equiv.Perm LorentzianIndex,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ index : LorentzianIndex,
            configuration.coframe point (σ index) index by
    funext point
    exact Matrix.det_apply' _]
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  exact smooth.1 (permutation index) index

theorem holonomicCoframe_adjugate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point => (configuration.coframe point).adjugate := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  rw [show (fun point => (configuration.coframe point).adjugate row column) =
      fun point => Matrix.det
        ((configuration.coframe point).updateRow column (Pi.single row 1)) by
    funext point
    exact Matrix.adjugate_apply _ _ _]
  rw [show (fun point => Matrix.det
      ((configuration.coframe point).updateRow column (Pi.single row 1))) =
      fun point => ∑ σ : Equiv.Perm LorentzianIndex,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ index : LorentzianIndex,
            (configuration.coframe point).updateRow column
              (Pi.single row 1) (σ index) index by
    funext point
    exact Matrix.det_apply' _]
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  by_cases updated : permutation index = column
  · rw [show (fun point : BasePoint =>
        (configuration.coframe point).updateRow column
          (Pi.single row (1 : ℝ)) (permutation index) index) =
      fun _ : BasePoint => if index = row then (1 : ℝ) else 0 by
        funext point
        simp [Matrix.updateRow_apply, updated, Pi.single_apply]]
    exact contDiff_const
  · simpa [Matrix.updateRow_apply, updated] using
      smooth.1 (permutation index) index

theorem holonomicCoframe_inv_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ fun point => (configuration.coframe point)⁻¹ := by
  rw [show (fun point => (configuration.coframe point)⁻¹) =
      fun point =>
        (Matrix.det (configuration.coframe point))⁻¹ •
          (configuration.coframe point).adjugate by
    funext point
    rw [Matrix.inv_def, Ring.inverse_eq_inv]]
  exact (holonomicCoframe_det_contDiff configuration smooth).inv
      nondegenerate |>.smul
        (holonomicCoframe_adjugate_contDiff configuration smooth)

theorem holonomicGeneratedVolumeDensity_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ fun point =>
      abs (Matrix.det (configuration.coframe point)) :=
  (holonomicCoframe_det_contDiff configuration smooth).abs nondegenerate

theorem coframeTwoFormLinear_apply_contDiff
    (coframe : BasePoint → LorentzianCoframe)
    (coframeSmooth : ContDiff ℝ ∞ coframe)
    (form : BasePoint → GaugeTwoForm)
    (formSmooth : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun point =>
      coframeTwoFormLinear (coframe point) (form point) := by
  apply contDiff_pi'
  intro outputPair
  change ContDiff ℝ ∞ fun point =>
    ∑ inputPair : Fin 6,
      coframeWedge (coframe point) outputPair inputPair * form point inputPair
  apply ContDiff.sum
  intro inputPair _
  have coframeEntrySmooth : ∀ row column,
      ContDiff ℝ ∞ fun point => coframe point row column :=
    fun row column =>
      contDiff_pi.mp (contDiff_pi.mp coframeSmooth row) column
  have formEntrySmooth : ∀ pair,
      ContDiff ℝ ∞ fun point => form point pair :=
    fun pair => contDiff_pi.mp formSmooth pair
  unfold coframeWedge
  fun_prop

theorem lorentzianCoframeHodge_apply_contDiff
    (form : BasePoint → GaugeTwoForm)
    (formSmooth : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun point => lorentzianCoframeHodge (form point) := by
  apply contDiff_pi'
  intro pair
  fin_cases pair <;>
    simp [lorentzianCoframeHodge] <;> fun_prop

theorem holonomicGaugeSpacetimeHodge_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (form : BasePoint → GaugeTwoForm)
    (formSmooth : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun point =>
      coframeGaugeSpacetimeHodgeLinear
        (configuration.coframe point) (form point) := by
  have coframeSmooth := holonomicCoframe_contDiff configuration smooth
  have forwardSmooth := coframeTwoFormLinear_apply_contDiff
    configuration.coframe coframeSmooth form formSmooth
  have fixedHodgeSmooth := lorentzianCoframeHodge_apply_contDiff
    (fun point => coframeTwoFormLinear
      (configuration.coframe point) (form point)) forwardSmooth
  have inverseSmooth := holonomicCoframe_inv_contDiff
    configuration smooth nondegenerate
  have pulledBackSmooth := coframeTwoFormLinear_apply_contDiff
    (fun point => (configuration.coframe point)⁻¹) inverseSmooth
    (fun point => lorentzianCoframeHodge
      (coframeTwoFormLinear (configuration.coframe point) (form point)))
    fixedHodgeSmooth
  simpa [coframeGaugeSpacetimeHodgeLinear,
    inverseCoframeTwoFormLinear, LinearMap.comp_apply,
    lorentzianCoframeHodgeEquiv] using pulledBackSmooth

theorem holonomicP286GaugeAuxiliaryCoordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate configuration) := by
  apply contDiff_pi'
  intro pair
  exact smooth.2.2.2.2.2.1 pair

theorem holonomicLiftCoframeTwoFormLinear_apply_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (form : BasePoint → P286GaugeTwoForm)
    (formSmooth : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun point =>
      liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point)) (form point) := by
  apply contDiff_pi'
  intro output
  unfold liftGaugeTwoFormOperator
  apply ContDiff.sum
  intro input _
  have coefficientSmooth : ContDiff ℝ ∞ fun point =>
      gaugeOperatorCoefficient
        (coframeTwoFormLinear (configuration.coframe point)) output input := by
    have coframeEntrySmooth : ∀ row column,
        ContDiff ℝ ∞ fun point =>
          configuration.coframe point row column := smooth.1
    have wedgeSmooth : ContDiff ℝ ∞ fun point =>
        coframeWedge (configuration.coframe point) output input := by
      unfold coframeWedge
      fun_prop
    simpa [gaugeOperatorCoefficient, coframeTwoFormLinear] using wedgeSmooth
  exact coefficientSmooth.smul (contDiff_pi.mp formSmooth input)

theorem liftGaugeTwoFormOperator_apply_contDiff_p286
    (operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (form : BasePoint → P286GaugeTwoForm)
    (formSmooth : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ fun point =>
      liftGaugeTwoFormOperator operator (form point) := by
  apply contDiff_pi'
  intro output
  unfold liftGaugeTwoFormOperator
  apply ContDiff.sum
  intro input _
  exact (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
      gaugeOperatorCoefficient operator output input).smul
    (contDiff_pi.mp formSmooth input)

theorem p286CoordinateLiePairing_apply_contDiff
    (first second : BasePoint → P286CoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateLiePairing (first point) (second point) := by
  have outerSmooth : ContDiff ℝ ∞ fun point =>
      p286CoordinateLiePairingBilinear.toContinuousBilinearMap
        (first point) :=
    contDiff_const.clm_apply firstSmooth
  have actual := outerSmooth.clm_apply secondSmooth
  exact actual

def p286GaugeConnectionBFDifferentialMomentum
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeTwoForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    p286GaugeAuxiliaryHodgePairingPolynomial
      (configuration.coframe point)
      (holonomicP286GaugeAuxiliaryCoordinate configuration point)
      direction

theorem p286GaugeConnectionBFDifferentialMomentum_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeTwoForm) :
    ContDiff ℝ ∞
      (p286GaugeConnectionBFDifferentialMomentum configuration direction) := by
  have auxiliarySmooth :=
    holonomicP286GaugeAuxiliaryCoordinate_contDiff configuration smooth
  have auxiliaryTransformSmooth :=
    holonomicLiftCoframeTwoFormLinear_apply_contDiff configuration smooth
      (holonomicP286GaugeAuxiliaryCoordinate configuration) auxiliarySmooth
  have directionTransformSmooth :=
    holonomicLiftCoframeTwoFormLinear_apply_contDiff configuration smooth
      (fun _ => direction) contDiff_const
  have hodgeDirectionTransformSmooth :=
    liftGaugeTwoFormOperator_apply_contDiff_p286 lorentzianCoframeHodge
      (fun point => liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point)) direction)
      directionTransformSmooth
  have volumeSmooth := holonomicGeneratedVolumeDensity_contDiff
    configuration smooth nondegenerate
  unfold p286GaugeConnectionBFDifferentialMomentum
    p286GaugeAuxiliaryHodgePairingPolynomial
  apply volumeSmooth.mul
  apply ContDiff.sum
  intro pair _
  apply contDiff_const.mul
  exact p286CoordinateLiePairing_apply_contDiff
    (fun point => liftGaugeTwoFormOperator
      (coframeTwoFormLinear (configuration.coframe point))
      (holonomicP286GaugeAuxiliaryCoordinate configuration point) pair)
    (fun point => liftGaugeTwoFormOperator lorentzianCoframeHodge
      (liftGaugeTwoFormOperator
        (coframeTwoFormLinear (configuration.coframe point)) direction) pair)
    (contDiff_pi.mp auxiliaryTransformSmooth pair)
    (contDiff_pi.mp hodgeDirectionTransformSmooth pair)

end

end SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionMomentumRegularity
