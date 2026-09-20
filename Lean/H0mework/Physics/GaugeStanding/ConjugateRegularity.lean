import H0mework.Physics.GaugeStanding.Variation

/-!
# S9-C: contragredient regularity for the linked active P286 path

This module constructs the actual coordinate action on conjugate matter from
the existing coordinate/dual equivalence and the actual P286 mother-Lie
action:

`(ε, barψ) ↦ coordinates (-(dual barψ) ∘ ρ(ε))`.

The construction is proved real-bilinear, hence continuous in the finite
coordinate carriers.  It then packages the conjugate component of the linked
active tangent as a compactly supported smooth primitive variation generated
by the same compact-smooth parameter.

No smoothness receipt, Ward identity, stationarity law, or residual-zero
premise is accepted.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveConjugateRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveVariation
open StageNineConjugateMatterVariation
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open DiracExteriorMatterAction
open scoped ContDiff

noncomputable section

set_option autoImplicit false

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286InfinitesimalGaugeTransformation.p286CoordinateIndexFintype

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Coordinate/dual linearity -/

theorem matterDualOfCoordinates_add_linked
    (first second : MatterCoordinateCarrier) :
    matterDualOfCoordinates (first + second) =
      matterDualOfCoordinates first + matterDualOfCoordinates second := by
  apply LinearMap.ext
  intro matter
  simp [matterDualOfCoordinates_apply, mul_add, Finset.sum_add_distrib]

theorem matterDualCoordinates_add_linked
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualCoordinates (first + second) =
      matterDualCoordinates first + matterDualCoordinates second := by
  apply PiLp.ext
  intro index
  simp [matterDualCoordinates]

theorem matterDualCoordinates_real_smul_linked
    (parameter : ℝ)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    matterDualCoordinates (parameter • dual) =
      parameter • matterDualCoordinates dual := by
  apply PiLp.ext
  intro index
  simp [matterDualCoordinates]

/-! ## Actual contragredient coordinate action -/

/-- Raw coordinate form of the actual infinitesimal contragredient action. -/
def p286ContragredientCoordinateAction
    (matrix : P286CoordinateCarrier)
    (coordinates : MatterCoordinateCarrier) : MatterCoordinateCarrier :=
  matterDualCoordinates
    (-(matterDualOfCoordinates coordinates).comp
      (diracExteriorMotherLieAction
        (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix))))

theorem p286ContragredientCoordinateAction_add_right
    (matrix : P286CoordinateCarrier)
    (first second : MatterCoordinateCarrier) :
    p286ContragredientCoordinateAction matrix (first + second) =
      p286ContragredientCoordinateAction matrix first +
        p286ContragredientCoordinateAction matrix second := by
  apply PiLp.ext
  intro index
  simp [p286ContragredientCoordinateAction, matterDualCoordinates,
    matterDualOfCoordinates_add_linked]
  all_goals abel

theorem p286ContragredientCoordinateAction_real_smul_right
    (matrix : P286CoordinateCarrier) (parameter : ℝ)
    (coordinates : MatterCoordinateCarrier) :
    p286ContragredientCoordinateAction matrix (parameter • coordinates) =
      parameter •
        p286ContragredientCoordinateAction matrix coordinates := by
  apply PiLp.ext
  intro index
  simp [p286ContragredientCoordinateAction, matterDualCoordinates,
    matterDualOfCoordinates_real_smul]

theorem p286ContragredientCoordinateAction_add_left
    (first second : P286CoordinateCarrier)
    (coordinates : MatterCoordinateCarrier) :
    p286ContragredientCoordinateAction (first + second) coordinates =
      p286ContragredientCoordinateAction first coordinates +
        p286ContragredientCoordinateAction second coordinates := by
  apply PiLp.ext
  intro index
  simp [p286ContragredientCoordinateAction, matterDualCoordinates,
    p286LieBlockEmbed_add, diracExteriorMotherLieAction_add]
  all_goals abel

theorem p286ContragredientCoordinateAction_real_smul_left
    (parameter : ℝ) (matrix : P286CoordinateCarrier)
    (coordinates : MatterCoordinateCarrier) :
    p286ContragredientCoordinateAction (parameter • matrix) coordinates =
      parameter •
        p286ContragredientCoordinateAction matrix coordinates := by
  apply PiLp.ext
  intro index
  simp [p286ContragredientCoordinateAction, matterDualCoordinates,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul]

/-- The actual contragredient action as a real bilinear map on the declared
finite coordinate carriers. -/
def p286ContragredientCoordinateBilinear :
    P286CoordinateCarrier →ₗ[ℝ]
      MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun matrix :=
    { toFun := p286ContragredientCoordinateAction matrix
      map_add' := p286ContragredientCoordinateAction_add_right matrix
      map_smul' :=
        p286ContragredientCoordinateAction_real_smul_right matrix }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro coordinates
    exact p286ContragredientCoordinateAction_add_left first second coordinates
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro coordinates
    exact p286ContragredientCoordinateAction_real_smul_left
      parameter matrix coordinates

@[simp] theorem p286ContragredientCoordinateBilinear_apply
    (matrix : P286CoordinateCarrier)
    (coordinates : MatterCoordinateCarrier) :
    p286ContragredientCoordinateBilinear matrix coordinates =
      matterDualCoordinates
        (-(matterDualOfCoordinates coordinates).comp
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (p286CoordinateEquiv.symm matrix)))) :=
  rfl

/-! ## Fidelity to the linked tangent -/

theorem p286ContragredientCoordinateBilinear_linkedTangent
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    p286ContragredientCoordinateBilinear (gaugeParameter point)
        (matterDualCoordinates (configuration.conjugateMatter point)) =
      matterDualCoordinates
        (representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).conjugateMatter := by
  simp [p286ContragredientCoordinateBilinear_apply,
    representationDerivedP286CoupledGaugeTangentSection,
    representationDerivedP286CoupledGaugeTangentAt,
    p286GaugeParameterMotherAt, matterDualOfCoordinates_surjective]

theorem configurationConjugateMatterCoordinates_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ fun point =>
      matterDualCoordinates (configuration.conjugateMatter point) := by
  let assemble : (MatterCoordinateIndex → ℂ) →L[ℝ]
      MatterCoordinateCarrier :=
    (EuclideanSpace.equiv MatterCoordinateIndex ℂ).symm.toContinuousLinearMap
      |>.restrictScalars ℝ
  have coordinateSmooth : ContDiff ℝ ∞ (fun point index =>
      configuration.conjugateMatter point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) := by
    apply contDiff_pi'
    intro index
    exact smooth.2.2.2.2.2.2.2.2 index
  have assembled := assemble.contDiff.comp coordinateSmooth
  rw [show (fun point =>
      matterDualCoordinates (configuration.conjugateMatter point)) =
    fun point =>
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).symm
        (fun index =>
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))) by
    funext point
    apply PiLp.ext
    intro index
    rfl]
  exact assembled

/-! ## Compact-smooth linked conjugate variation -/

/-- Compact-smooth coordinates of the linked contragredient tangent.  Both
arguments are generated internally from the same configuration and local
parameter. -/
def p286LinkedActiveConjugateMatterVariation
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    CompactlySupportedSmoothVariation MatterCoordinateCarrier where
  toFun := fun point =>
    p286ContragredientCoordinateBilinear (gaugeParameter point)
      (matterDualCoordinates (configuration.conjugateMatter point))
  smooth :=
    (p286ContragredientCoordinateBilinear.toContinuousBilinearMap.contDiff.comp
      gaugeParameter.smooth).clm_apply
      (configurationConjugateMatterCoordinates_contDiff configuration smooth)
  compactSupport := by
    have parameterEventually := gaugeParameter.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at parameterEventually ⊢
    filter_upwards [parameterEventually] with point parameterZero
    have parameterZero' : gaugeParameter point = 0 := by
      simpa using parameterZero
    simp [parameterZero']

@[simp] theorem p286LinkedActiveConjugateMatterVariation_apply
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    p286LinkedActiveConjugateMatterVariation configuration smooth
        gaugeParameter point =
      matterDualCoordinates
        (representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).conjugateMatter :=
  p286ContragredientCoordinateBilinear_linkedTangent
    configuration gaugeParameter point

theorem p286LinkedActiveConjugateMatterVariation_dual_fidelity
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    matterDualOfCoordinates
        (p286LinkedActiveConjugateMatterVariation configuration smooth
          gaugeParameter point) =
      (representationDerivedP286CoupledGaugeTangentSection configuration
        gaugeParameter point).conjugateMatter := by
  rw [p286LinkedActiveConjugateMatterVariation_apply,
    matterDualOfCoordinates_surjective]

end

end SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveConjugateRegularity
