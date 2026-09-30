import H0mework.Physics.DiracEvolution.SafeWeakEnergyRate

/-!
# Fixed P506/L0 mode-uniform weak energy estimate

The same Cauchy-safe mother-action coefficients that generate the finite weak
mass and stiffness forms also generate a quadratic rate bound before any mode
count is selected.  Compact support in one common spatial box removes the
boundary flux, and the generated rate bound feeds the finite weak equation to
produce a mode-uniform Grönwall estimate.  Compact positivity of the same time
principal generates strict coercivity and the resulting spatial `L²` bound
with constants fixed before the finite carrier is selected.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate

open MeasureTheory Set
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterSymmetricHyperbolicFluxBalance
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterSpatialEnergyTimeDerivative
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeCauchySafeMatterDifferentialOperator
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open DiracCliffordRepresentation
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open scoped ComplexOrder ContDiff Matrix Matrix.Norms.Elementwise NNReal

noncomputable section

set_option autoImplicit false

variable {modeCount : ℕ}

private def complexMulRealBilinear : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℂ :=
  LinearMap.mul ℝ ℂ

private def fiberCoefficient
    (field : DiracExteriorMatterCarrier) :
    DiracMatterGalerkinCoefficient 1 :=
  WithLp.toLp 2 fun index ↦ matterCoordinateEquiv field index.2

private theorem fiberCoefficient_norm
    (field : DiracExteriorMatterCarrier) :
    ‖fiberCoefficient field‖ = ‖matterCoordinateEquiv field‖ := by
  rw [PiLp.norm_eq_sum (by norm_num)]
  rw [PiLp.norm_eq_sum (by norm_num)]
  congr 1
  rw [Fintype.sum_prod_type]
  simp [fiberCoefficient]

private def fiberCoefficientLinear :
    MatterCoordinateCarrier →ₗ[ℝ] DiracMatterGalerkinCoefficient 1 where
  toFun coordinates := WithLp.toLp 2 fun index ↦ coordinates index.2
  map_add' first second := by
    apply PiLp.ext
    intro index
    rfl
  map_smul' parameter coordinates := by
    apply PiLp.ext
    intro index
    rfl

private def fiberCoefficientCLM :
    MatterCoordinateCarrier →L[ℝ] DiracMatterGalerkinCoefficient 1 :=
  ⟨fiberCoefficientLinear,
    fiberCoefficientLinear.continuous_of_finiteDimensional⟩

theorem fiberCoefficient_eq_clm
    (field : DiracExteriorMatterCarrier) :
    fiberCoefficient field = fiberCoefficientCLM (matterCoordinateEquiv field) :=
  rfl

@[simp] private theorem fiberCoefficient_mode_zero
    (field : DiracExteriorMatterCarrier) :
    diracMatterGalerkinCoefficientMode (fiberCoefficient field) 0 =
      matterCoordinateEquiv field := by
  ext coordinate
  rfl

private theorem constantSpatialSynthesis_fiberCoefficient
    (field : DiracExteriorMatterCarrier)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialGalerkinSynthesis
        (fun _mode : Fin 1 ↦ fun _space : DiracMatterSpatialCoordinates ↦ 1)
        (fiberCoefficient field) space = field := by
  apply matterCoordinateEquiv.injective
  ext coordinate
  rw [diracMatterSpatialGalerkinSynthesis_coordinates, Fin.sum_univ_one]
  simp [fiberCoefficient, diracMatterGalerkinCoefficientMode]

private theorem constantCauchySynthesis_fiberCoefficient
    (field : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    cauchySafeMatterGalerkinSynthesis
        (fun _mode : Fin 1 ↦ fun _point : BasePoint ↦ 1)
        (fiberCoefficient field) point = field := by
  apply matterCoordinateEquiv.injective
  rw [cauchySafeMatterGalerkinSynthesis_coordinates, Fin.sum_univ_one]
  simp [fiberCoefficient, diracMatterGalerkinCoefficientMode]

private abbrev FixedCurrent : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

private def constantField
    (field : DiracExteriorMatterCarrier) :
    BasePoint → DiracExteriorMatterCarrier :=
  fun _point ↦ field

private def centeredField
    (field : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint) : BasePoint → DiracExteriorMatterCarrier :=
  fun candidate ↦ field candidate - field point

private def rawDirectionalDerivative
    (field : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (fieldDirectionalDerivative
      (fun candidate ↦ matterCoordinateEquiv (field candidate)) point
      direction)

private def internalMatterCoordinateOfCoordinatesLinear
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex) :
    MatterCoordinateCarrier →ₗ[ℂ] ℂ where
  toFun coordinates :=
    internalMatterCoordinate internal (matterCoordinateEquiv.symm coordinates spin)
  map_add' first second := by simp [internalMatterCoordinate]
  map_smul' parameter coordinates := by simp [internalMatterCoordinate]

private def internalMatterCoordinateOfCoordinatesCLM
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex) :
    MatterCoordinateCarrier →L[ℝ] ℂ := by
  letI : AddCommGroup ℂ :=
    Complex.instNormedAddCommGroup.toAddCommGroup
  exact
    (internalMatterCoordinateOfCoordinatesLinear internal spin
      ).toContinuousLinearMap.restrictScalars ℝ

private theorem fixedWeakSpatialCandidate_internalCoordinate_hasDerivAt
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex) :
    HasDerivAt
      (fun parameter ↦
        internalMatterCoordinate internal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
            (diracMatterCoordinateLine point direction parameter) spin))
      (internalMatterCoordinate internal
        (rawDirectionalDerivative
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
          point direction spin))
      0 := by
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  have coordinatesDifferentiable : Differentiable ℝ
      (fun candidate ↦ matterCoordinateEquiv (field candidate)) :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate_differentiable basis
      basisRegular coefficient
  have coordinateLineDerivative :=
    coordinatesDifferentiable.differentiableAt.hasFDerivAt.comp_hasDerivAt 0
    (diracMatterCoordinateLine_hasDerivAt point direction)
  have coordinateDerivative :=
    (internalMatterCoordinateOfCoordinatesCLM internal spin).hasFDerivAt
      |>.comp_hasDerivAt 0 coordinateLineDerivative
  have lineZero :
      diracMatterCoordinateLine point direction 0 = point := by
    simp [diracMatterCoordinateLine]
  rw [lineZero] at coordinateDerivative
  have clmApply (coordinates : MatterCoordinateCarrier) :
      internalMatterCoordinateOfCoordinatesCLM internal spin coordinates =
        internalMatterCoordinate internal
          (matterCoordinateEquiv.symm coordinates spin) := by
    rfl
  have functionEquality :
      (fun parameter ↦
        internalMatterCoordinate internal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
            (diracMatterCoordinateLine point direction parameter) spin)) =
        (internalMatterCoordinateOfCoordinatesCLM internal spin ∘
          (fun candidate ↦ matterCoordinateEquiv (field candidate)) ∘
            diracMatterCoordinateLine point direction) := by
    funext parameter
    rw [Function.comp_apply, Function.comp_apply, clmApply]
    simp [field]
  rw [functionEquality]
  convert coordinateDerivative using 1
  all_goals rfl

private theorem diracMatterSpacetimeCoordinatePoint_sliceDirection
    (time parameter : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (direction : LorentzianIndex) :
    diracMatterSpacetimeCoordinatePoint
        ((time, space) + parameter • diracMatterSliceDirection direction).1
        ((time, space) + parameter • diracMatterSliceDirection direction).2 =
      diracMatterCoordinateLine
        (diracMatterSpacetimeCoordinatePoint time space)
        direction parameter := by
  refine Fin.cases ?_ (fun spatialDirection ↦ ?_) direction
  · apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [diracMatterSliceDirection, diracMatterSpacetimeCoordinatePoint,
        diracMatterCoordinateLine, canonicalCauchySlicePoint,
        canonicalLorentzianTimeDirection, coordinateDirection,
        Fin.sum_univ_three]
  · simpa [diracMatterSliceDirection] using
      diracMatterSpacetimeCoordinatePoint_line time space spatialDirection
        parameter

private theorem fixedEvolutionPrincipal_entry_coordinate_hasDerivAt
    (direction : LorentzianIndex)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (row column : LorentzianIndex) :
    HasDerivAt
      (fun parameter ↦
        fixedEvolutionPrincipal direction
          (diracMatterCoordinateLine
            (diracMatterSpacetimeCoordinatePoint time space)
            direction parameter) row column)
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction
        time space row column)
      0 := by
  let base : ℝ × DiracMatterSpatialCoordinates := (time, space)
  let sliceDirection := diracMatterSliceDirection direction
  let directionLinear : ℝ →L[ℝ]
      (ℝ × DiracMatterSpatialCoordinates) :=
    (1 : ℝ →L[ℝ] ℝ).smulRight sliceDirection
  let sliceLine : ℝ → ℝ × DiracMatterSpatialCoordinates :=
    fun parameter ↦ base + directionLinear parameter
  let entry : (ℝ × DiracMatterSpatialCoordinates) → ℂ :=
    fun input ↦ fixedEvolutionPrincipalOnSlice direction
      input.1 input.2 row column
  have sliceLineDerivative : HasDerivAt sliceLine sliceDirection 0 := by
    have actual := (hasDerivAt_const (x := (0 : ℝ)) base).add
      directionLinear.hasFDerivAt.hasDerivAt
    exact actual.congr_deriv (by simp [directionLinear, sliceDirection])
  have entryDerivative : HasDerivAt (entry ∘ sliceLine)
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction
        time space row column) 0 := by
    have outer :=
      ((fixedEvolutionPrincipalOnSlice_entry_contDiff direction row column).of_le
        (by norm_num)).differentiable one_ne_zero base
    have outerAtLineZero : HasFDerivAt entry
        (fderiv ℝ entry base) (sliceLine 0) := by
      simpa [entry, sliceLine] using outer.hasFDerivAt
    have composed := outerAtLineZero.comp_hasDerivAt 0 sliceLineDerivative
    simpa [entry, base, fixedEvolutionPrincipalDirectionalDerivativeOnSlice,
      sliceDirection] using composed
  have curveEq :
      entry ∘ sliceLine =
        fun parameter ↦
          fixedEvolutionPrincipal direction
            (diracMatterCoordinateLine
              (diracMatterSpacetimeCoordinatePoint time space)
              direction parameter) row column := by
    funext parameter
    unfold entry fixedEvolutionPrincipalOnSlice
    apply congrArg
      (fun point : BasePoint ↦ fixedEvolutionPrincipal direction point row column)
    have sliceLineEq :
        sliceLine parameter =
          (time, space) + parameter • diracMatterSliceDirection direction := by
      ext <;>
        simp [sliceLine, base, directionLinear, sliceDirection]
    rw [sliceLineEq]
    exact diracMatterSpacetimeCoordinatePoint_sliceDirection time parameter
      space direction
  rw [curveEq] at entryDerivative
  exact entryDerivative

private theorem fixedWeakSpatialCandidate_actedInternalCoordinate_hasDerivAt
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (direction : LorentzianIndex)
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex) :
    let point := diracMatterSpacetimeCoordinatePoint time space
    let field :=
      fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
    let fieldDerivative := rawDirectionalDerivative field point direction
    let coefficientDerivative :=
      fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction time space
    HasDerivAt
      (fun parameter ↦
        internalMatterCoordinate internal
          (diracMatrixMatterAction
            (fixedEvolutionPrincipal direction
              (diracMatterCoordinateLine point direction parameter))
            (field (diracMatterCoordinateLine point direction parameter))
            spin))
      (internalMatterCoordinate internal
        ((diracMatrixMatterAction
            (fixedEvolutionPrincipal direction point) fieldDerivative +
          diracMatrixMatterAction coefficientDerivative (field point)) spin))
      0 := by
  dsimp only
  let point := diracMatterSpacetimeCoordinatePoint time space
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  let fieldDerivative := rawDirectionalDerivative field point direction
  let coefficientDerivative :=
    fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction time space
  have summandDerivative (column : DiracSpinorIndex) : HasDerivAt
      (fun parameter ↦
        fixedEvolutionPrincipal direction
            (diracMatterCoordinateLine point direction parameter) spin column *
          internalMatterCoordinate internal
            (field (diracMatterCoordinateLine point direction parameter)
              column))
      (coefficientDerivative spin column *
          internalMatterCoordinate internal (field point column) +
        fixedEvolutionPrincipal direction point spin column *
          internalMatterCoordinate internal (fieldDerivative column))
      0 := by
    have firstDerivative :=
      fixedEvolutionPrincipal_entry_coordinate_hasDerivAt direction time space
        spin column
    have secondDerivative :=
      fixedWeakSpatialCandidate_internalCoordinate_hasDerivAt basis
        basisRegular coefficient point direction internal column
    have outerDerivative :=
      complexMulRealBilinear.toContinuousBilinearMap.hasFDerivAt
        |>.comp_hasDerivAt 0 firstDerivative
    have productDerivative := outerDerivative.clm_apply secondDerivative
    simpa [point, field, fieldDerivative, coefficientDerivative,
      complexMulRealBilinear] using productDerivative
  have sumDerivative := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun column parameter ↦
      fixedEvolutionPrincipal direction
          (diracMatterCoordinateLine point direction parameter) spin column *
        internalMatterCoordinate internal
          (field (diracMatterCoordinateLine point direction parameter) column))
    (A' := fun column ↦
      coefficientDerivative spin column *
          internalMatterCoordinate internal (field point column) +
        fixedEvolutionPrincipal direction point spin column *
          internalMatterCoordinate internal (fieldDerivative column))
    (x := 0) (fun column _ ↦ summandDerivative column)
  have functionEq :
      (fun parameter ↦
        internalMatterCoordinate internal
          (diracMatrixMatterAction
            (fixedEvolutionPrincipal direction
              (diracMatterCoordinateLine point direction parameter))
            (field (diracMatterCoordinateLine point direction parameter)) spin)) =
        fun parameter ↦ ∑ column : DiracSpinorIndex,
          fixedEvolutionPrincipal direction
              (diracMatterCoordinateLine point direction parameter) spin column *
            internalMatterCoordinate internal
              (field (diracMatterCoordinateLine point direction parameter)
                column) := by
    funext parameter
    exact internalMatterCoordinate_diracMatrixMatterAction _ _ spin internal
  rw [functionEq]
  convert sumDerivative using 1
  all_goals try rfl
  · rw [Pi.add_apply, map_add,
      Finset.sum_add_distrib]
    rw [internalMatterCoordinate_diracMatrixMatterAction
      coefficientDerivative (field point) spin internal]
    rw [internalMatterCoordinate_diracMatrixMatterAction
      (fixedEvolutionPrincipal direction point) fieldDerivative spin internal]
    ac_rfl

private theorem fixedConstantActionResponse_fiberCoefficient
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (field : DiracExteriorMatterCarrier) :
    fixedConstantActionResponse time (fiberCoefficient field) space =
      cauchySafeMatterVolterraVelocity FixedCurrent (constantField field)
        (diracMatterSpacetimeCoordinatePoint time space) := by
  unfold fixedConstantActionResponse
  change cauchySafeMatterVolterraVelocity FixedCurrent
      (cauchySafeMatterGalerkinSynthesis
        (fun _mode : Fin 1 ↦ fun _point : BasePoint ↦ 1)
        (fiberCoefficient field))
      (diracMatterSpacetimeCoordinatePoint time space) = _
  congr 1
  funext point
  exact constantCauchySynthesis_fiberCoefficient field point

private theorem fixedActionResponse_eq_constant_add_centered
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    fixedP506L0CauchySafeMatterWeakActionResponse basis time coefficient space =
      fixedConstantActionResponse time
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis coefficient space))
          space +
        cauchySafeMatterVolterraVelocity FixedCurrent
          (centeredField
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
            (diracMatterSpacetimeCoordinatePoint time space))
          (diracMatterSpacetimeCoordinatePoint time space) := by
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  let point := diracMatterSpacetimeCoordinatePoint time space
  have fieldAt : field point =
      diracMatterSpatialGalerkinSynthesis basis coefficient space := by
    exact fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice basis
      coefficient time space
  have fieldCoordinatesDifferentiable : Differentiable ℝ
      (fun candidate ↦ matterCoordinateEquiv (field candidate)) := by
    exact fixedP506L0CauchySafeMatterWeakSpatialCandidate_differentiable basis
      basisRegular coefficient
  have constantDifferentiable : DifferentiableAt ℝ
      (fun candidate ↦ matterCoordinateEquiv
        (constantField (field point) candidate)) point := by
    simpa [constantField] using
      (differentiableAt_const (c := matterCoordinateEquiv (field point)))
  have centeredDifferentiable : DifferentiableAt ℝ
      (fun candidate ↦ matterCoordinateEquiv
        (centeredField field point candidate)) point := by
    simpa [centeredField, map_sub] using
      (fieldCoordinatesDifferentiable.differentiableAt.sub
        (differentiableAt_const (c := matterCoordinateEquiv (field point))))
  have fieldDecomposition :
      field = constantField (field point) + centeredField field point := by
    funext candidate
    simp [constantField, centeredField]
  change cauchySafeMatterVolterraVelocity FixedCurrent field point = _
  rw [fieldDecomposition,
    cauchySafeMatterVolterraVelocity_add FixedCurrent
      (constantField (field point)) (centeredField field point) point
      constantDifferentiable centeredDifferentiable]
  rw [fieldAt, fixedConstantActionResponse_fiberCoefficient]

private theorem centeredVolterraVelocity_coordinateLaw
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    let field :=
      fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
    let point := diracMatterSpacetimeCoordinatePoint time space
    let centered := centeredField field point
    diracMatrixMatterAction
          (coframeCoordinateDiracEvolutionPrincipal
            (FixedCurrent.coframe point) 0)
          (matterCoordinateEquiv.symm
            (cauchySafeMatterVolterraVelocity FixedCurrent centered point)) +
        ∑ direction : Fin 3,
          diracMatrixMatterAction
            (coframeCoordinateDiracEvolutionPrincipal
              (FixedCurrent.coframe point) direction.succ)
            (rawDirectionalDerivative centered point direction.succ) =
      0 := by
  dsimp only
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  let point := diracMatterSpacetimeCoordinatePoint time space
  let centered := centeredField field point
  let actual := cauchySafeMatterCandidateActual FixedCurrent centered
  have centeredAt : centered point = 0 := by
    simp [centered, centeredField]
  have actualNoncharacteristic :
      coframeTemporalPrincipalScalar (actual.coframe point) ≠ 0 := by
    change coframeTemporalPrincipalScalar (FixedCurrent.coframe point) ≠ 0
    rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
    exact
      fixedP506L0CartanECConstraintCauchySafeGlobalActual_noncharacteristic
        point
  have actionLaw :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      actual point actualNoncharacteristic
  have connectionZero (direction : LorentzianIndex) :
      holonomicMatterConnectionAction actual point direction = 0 := by
    simp [holonomicMatterConnectionAction, actual,
      cauchySafeMatterCandidateActual, centeredAt]
  have timeDerivativeEq :
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          actual point =
        matterCoordinateEquiv.symm
          (cauchySafeMatterVolterraVelocity FixedCurrent centered point) := by
    unfold cauchySafeMatterVolterraVelocity
    rw [matterCoordinateEquiv.symm_apply_apply]
    unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    rw [connectionZero, sub_zero]
  have spatialDerivativeEq (direction : Fin 3) :
      holonomicMatterCovariantDerivative actual point direction.succ =
        rawDirectionalDerivative centered point direction.succ := by
    simp [holonomicMatterCovariantDerivative, actual,
      cauchySafeMatterCandidateActual, centeredAt, rawDirectionalDerivative]
  change CurrentCoframeMatterTemporalActionLaw (actual.coframe point)
      (holonomicDiracDualCurrentCoframeMatterKnownVector actual point)
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        actual point) at actionLaw
  have transformed := congrArg identityCoframeMatterTimePrincipal actionLaw
  have timeTransform :
      identityCoframeMatterTimePrincipal
          (currentCoframeMatterTemporalPrincipal (actual.coframe point)
            (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
              actual point)) =
        diracMatrixMatterAction
          (coframeCoordinateDiracEvolutionPrincipal
            (FixedCurrent.coframe point) 0)
          (matterCoordinateEquiv.symm
            (cauchySafeMatterVolterraVelocity FixedCurrent centered point)) := by
    unfold currentCoframeMatterTemporalPrincipal
    rw [timeDerivativeEq]
    exact identityCoframeMatterTimePrincipal_coordinatePrincipal
      (FixedCurrent.coframe point) 0 _
  have identityAdd (first second : DiracExteriorMatterCarrier) :
      identityCoframeMatterTimePrincipal (first + second) =
        identityCoframeMatterTimePrincipal first +
          identityCoframeMatterTimePrincipal second := by
    simp [identityCoframeMatterTimePrincipal]
  have identityZero :
      identityCoframeMatterTimePrincipal
          (0 : DiracExteriorMatterCarrier) = 0 := by
    simp [identityCoframeMatterTimePrincipal]
  have identitySpatialSum
      (fields : Fin 3 → DiracExteriorMatterCarrier) :
      identityCoframeMatterTimePrincipal
          (Complex.I • ∑ direction, fields direction) =
        ∑ direction,
          identityCoframeMatterTimePrincipal
            (Complex.I • fields direction) := by
    simp [identityCoframeMatterTimePrincipal, Finset.smul_sum, map_sum]
  have knownTransform :
      identityCoframeMatterTimePrincipal
          (holonomicDiracDualCurrentCoframeMatterKnownVector actual point) =
        ∑ direction : Fin 3,
          diracMatrixMatterAction
            (coframeCoordinateDiracEvolutionPrincipal
              (FixedCurrent.coframe point) direction.succ)
            (rawDirectionalDerivative centered point direction.succ) := by
    unfold holonomicDiracDualCurrentCoframeMatterKnownVector
    rw [identityAdd]
    have yukawaZero :
        diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (actual.scalar point))
            (actual.matter point) = 0 := by
      simp [actual, cauchySafeMatterCandidateActual, centeredAt]
    rw [yukawaZero, identityZero, add_zero, identitySpatialSum]
    apply Finset.sum_congr rfl
    intro direction _
    rw [spatialDerivativeEq direction]
    exact identityCoframeMatterTimePrincipal_coordinatePrincipal
      (FixedCurrent.coframe point) direction.succ _
  change identityCoframeMatterTimePrincipal
      (currentCoframeMatterTemporalPrincipal (actual.coframe point)
          (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
            actual point) +
        holonomicDiracDualCurrentCoframeMatterKnownVector actual point) =
      identityCoframeMatterTimePrincipal 0 at transformed
  rw [identityAdd, timeTransform, knownTransform, identityZero] at transformed
  exact transformed

private def spatialPrincipalPairing
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  let point := diracMatterSpacetimeCoordinatePoint time space
  let centered := centeredField field point
  ∑ direction : Fin 3,
    diracExteriorMatterEnergyPairing
      (fixedEvolutionPrincipal direction.succ point)
      (diracMatterSpatialGalerkinSynthesis basis coefficient space)
      (rawDirectionalDerivative centered point direction.succ)

private theorem fixedWeakStiffnessDensity_eq_constant_add_spatialPrincipal
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterWeakStiffnessDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
        (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
        coefficient coefficient space =
      diracMatterWeakStiffnessDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix time)
          (fun _mode : Fin 1 ↦
            fun _space : DiracMatterSpatialCoordinates ↦ 1)
          (fixedConstantActionResponse time)
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis coefficient space))
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis coefficient space))
          space +
        spatialPrincipalPairing basis coefficient time space := by
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  let point := diracMatterSpacetimeCoordinatePoint time space
  let centered := centeredField field point
  let localField :=
    diracMatterSpatialGalerkinSynthesis basis coefficient space
  have responseEq :=
    fixedActionResponse_eq_constant_add_centered basis basisRegular coefficient
      time space
  have carrierResponseEq :
      matterCoordinateEquiv.symm
          (fixedP506L0CauchySafeMatterWeakActionResponse basis time coefficient
            space) =
        matterCoordinateEquiv.symm
            (fixedConstantActionResponse time (fiberCoefficient localField)
              space) +
          matterCoordinateEquiv.symm
            (cauchySafeMatterVolterraVelocity FixedCurrent centered point) := by
    rw [responseEq, map_add]
  have centeredLaw :=
    centeredVolterraVelocity_coordinateLaw basis coefficient time space
  have pairingLaw := congrArg
    (fun result : DiracExteriorMatterCarrier ↦
      Complex.re (diracExteriorMatterCoordinatePairing localField result))
    centeredLaw
  change
    Complex.re
        ((diracExteriorMatterCoordinatePairingRight localField)
          ((diracMatrixMatterAction
              (coframeCoordinateDiracEvolutionPrincipal
                (FixedCurrent.coframe point) 0)
              (matterCoordinateEquiv.symm
                (cauchySafeMatterVolterraVelocity FixedCurrent centered point))) +
            ∑ direction : Fin 3,
              diracMatrixMatterAction
                (coframeCoordinateDiracEvolutionPrincipal
                  (FixedCurrent.coframe point) direction.succ)
                (rawDirectionalDerivative centered point direction.succ))) =
      Complex.re
        ((diracExteriorMatterCoordinatePairingRight localField) 0) at pairingLaw
  rw [map_add, map_sum, Complex.add_re, Complex.re_sum] at pairingLaw
  have pairingRightZero :
      (diracExteriorMatterCoordinatePairingRight localField) 0 = 0 :=
    map_zero _
  rw [pairingRightZero, Complex.zero_re] at pairingLaw
  have pairingLaw' :
      diracExteriorMatterEnergyPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
            localField
            (matterCoordinateEquiv.symm
              (cauchySafeMatterVolterraVelocity FixedCurrent centered point)) +
          spatialPrincipalPairing basis coefficient time space =
        0 := by
    change
      Complex.re
          (diracExteriorMatterCoordinatePairing localField
            (diracMatrixMatterAction
              (coframeCoordinateDiracEvolutionPrincipal
                (FixedCurrent.coframe point) 0)
              (matterCoordinateEquiv.symm
                (cauchySafeMatterVolterraVelocity FixedCurrent centered
                  point)))) +
        ∑ direction : Fin 3,
          Complex.re
            (diracExteriorMatterCoordinatePairing localField
              (diracMatrixMatterAction
                (coframeCoordinateDiracEvolutionPrincipal
                  (FixedCurrent.coframe point) direction.succ)
                (rawDirectionalDerivative centered point direction.succ))) =
        0
    exact pairingLaw
  unfold diracMatterWeakStiffnessDensity
  rw [carrierResponseEq, diracExteriorMatterEnergyPairing_add_right,
    constantSpatialSynthesis_fiberCoefficient]
  linarith

private theorem fixedPointwiseEnergy_fiberCoefficient
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    fixedPointwiseEnergy (time, space)
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis coefficient space)) =
      diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis coefficient
        coefficient space := by
  unfold fixedPointwiseEnergy fixedPointwiseEnergyForm
  change diracMatterWeakMassDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      (fun _mode : Fin 1 ↦ fun _space : DiracMatterSpatialCoordinates ↦ 1)
      (fiberCoefficient
        (diracMatterSpatialGalerkinSynthesis basis coefficient space))
      (fiberCoefficient
        (diracMatterSpatialGalerkinSynthesis basis coefficient space)) space = _
  unfold diracMatterWeakMassDensity
  rw [constantSpatialSynthesis_fiberCoefficient]

private theorem fixedSpatialEnergyFlux_eq_weakMassDensity
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (direction : Fin 3) :
    diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
        time direction =
      diracMatterWeakMassDensity
        (fixedEvolutionPrincipalOnSlice direction.succ time)
        basis coefficient coefficient := by
  funext space
  simp only [diracMatterSpatialEnergyFlux]
  change diracExteriorMatterCoordinateEnergy
      (fixedEvolutionPrincipal direction.succ
        (diracMatterSpacetimeCoordinatePoint time space))
      (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
        (diracMatterSpacetimeCoordinatePoint time space)) = _
  rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice]
  rfl

private theorem fixedSpatialEnergyFlux_contDiff_one
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (direction : Fin 3) :
    ContDiff ℝ 1
      (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
        time direction) := by
  have joint := diracMatterWeakMassDensity_joint_contDiff_one
    (fixedEvolutionPrincipalOnSlice direction.succ) basis
    (fun row column ↦
      (fixedEvolutionPrincipalOnSlice_entry_contDiff direction.succ row column).of_le
        (by norm_num))
    basisRegular coefficient coefficient
  have timeSlice : ContDiff ℝ 1
      (fun space : DiracMatterSpatialCoordinates ↦ (time, space)) :=
    (contDiff_const : ContDiff ℝ 1
      (fun _space : DiracMatterSpatialCoordinates ↦ time)).prodMk contDiff_id
  have restricted := joint.comp timeSlice
  convert restricted using 1
  exact fixedSpatialEnergyFlux_eq_weakMassDensity basis coefficient time direction

private theorem fixedSpatialBilinearFlux_eq_weakMassDensity
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (direction : Fin 3) :
    diracMatterSpatialBilinearFlux fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first)
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second)
        time direction =
      diracMatterWeakMassDensity
        (fixedEvolutionPrincipalOnSlice direction.succ time)
        basis first second := by
  funext space
  simp only [diracMatterSpatialBilinearFlux]
  rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice,
    fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice]
  rfl

private theorem fixedSpatialBilinearFlux_contDiff_one
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (direction : Fin 3) :
    ContDiff ℝ 1
      (diracMatterSpatialBilinearFlux fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first)
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second)
        time direction) := by
  have joint := diracMatterWeakMassDensity_joint_contDiff_one
    (fixedEvolutionPrincipalOnSlice direction.succ) basis
    (fun row column ↦
      (fixedEvolutionPrincipalOnSlice_entry_contDiff direction.succ row column).of_le
        (by norm_num))
    basisRegular first second
  have timeSlice : ContDiff ℝ 1
      (fun space : DiracMatterSpatialCoordinates ↦ (time, space)) :=
    (contDiff_const : ContDiff ℝ 1
      (fun _space : DiracMatterSpatialCoordinates ↦ time)).prodMk contDiff_id
  have restricted := joint.comp timeSlice
  convert restricted using 1
  exact fixedSpatialBilinearFlux_eq_weakMassDensity basis first second time
    direction

private theorem rawDirectionalDerivative_centeredField
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    rawDirectionalDerivative
        (centeredField
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
          point)
        point direction =
      rawDirectionalDerivative
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
        point direction := by
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  have fieldDifferentiable : DifferentiableAt ℝ
      (fun candidate ↦ matterCoordinateEquiv (field candidate)) point :=
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate_differentiable basis
      basisRegular coefficient).differentiableAt
  have constantDifferentiable : DifferentiableAt ℝ
      (fun _candidate : BasePoint ↦ matterCoordinateEquiv (field point)) point :=
    differentiableAt_const _
  have derivativeSub := fderiv_fun_sub fieldDifferentiable constantDifferentiable
  unfold rawDirectionalDerivative centeredField fieldDirectionalDerivative
  simp only [map_sub]
  rw [derivativeSub]
  simp
  rfl

private def spatialBilinearPrincipalPairing
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  let point := diracMatterSpacetimeCoordinatePoint time space
  let secondField :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second
  ∑ direction : Fin 3,
    diracMatterBilinearFlux
      (fixedEvolutionPrincipal direction.succ point)
      (diracMatterSpatialGalerkinSynthesis basis first space)
      (rawDirectionalDerivative secondField point direction.succ)

private def fixedWeakConstantStiffnessDensity
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  -diracMatterBilinearFlux
    (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
    (diracMatterSpatialGalerkinSynthesis basis first space)
    (matterCoordinateEquiv.symm
      (fixedConstantActionResponse time
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis second space))
        space))

private theorem fixedWeakStiffnessDensity_eq_constant_add_bilinearPrincipal
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterWeakStiffnessDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
        (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
        first second space =
      fixedWeakConstantStiffnessDensity basis first second time space +
        spatialBilinearPrincipalPairing basis first second time space := by
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second
  let point := diracMatterSpacetimeCoordinatePoint time space
  let centered := centeredField field point
  let firstField :=
    diracMatterSpatialGalerkinSynthesis basis first space
  let secondField :=
    diracMatterSpatialGalerkinSynthesis basis second space
  have responseEq :=
    fixedActionResponse_eq_constant_add_centered basis basisRegular second
      time space
  have carrierResponseEq :
      matterCoordinateEquiv.symm
          (fixedP506L0CauchySafeMatterWeakActionResponse basis time second
            space) =
        matterCoordinateEquiv.symm
            (fixedConstantActionResponse time (fiberCoefficient secondField)
              space) +
          matterCoordinateEquiv.symm
            (cauchySafeMatterVolterraVelocity FixedCurrent centered point) := by
    rw [responseEq, map_add]
  have centeredLaw :=
    centeredVolterraVelocity_coordinateLaw basis second time space
  have pairingLaw := congrArg
    (fun result : DiracExteriorMatterCarrier ↦
      Complex.re (diracExteriorMatterCoordinatePairing firstField result))
    centeredLaw
  change
    Complex.re
        ((diracExteriorMatterCoordinatePairingRight firstField)
          ((diracMatrixMatterAction
              (coframeCoordinateDiracEvolutionPrincipal
                (FixedCurrent.coframe point) 0)
              (matterCoordinateEquiv.symm
                (cauchySafeMatterVolterraVelocity FixedCurrent centered point))) +
            ∑ direction : Fin 3,
              diracMatrixMatterAction
                (coframeCoordinateDiracEvolutionPrincipal
                  (FixedCurrent.coframe point) direction.succ)
                (rawDirectionalDerivative centered point direction.succ))) =
      Complex.re
        ((diracExteriorMatterCoordinatePairingRight firstField) 0) at pairingLaw
  rw [map_add, map_sum, Complex.add_re, Complex.re_sum] at pairingLaw
  have pairingRightZero :
      (diracExteriorMatterCoordinatePairingRight firstField) 0 = 0 :=
    map_zero _
  rw [pairingRightZero, Complex.zero_re] at pairingLaw
  have principalEq :
      spatialBilinearPrincipalPairing basis first second time space =
        ∑ direction : Fin 3,
          diracMatterBilinearFlux
            (fixedEvolutionPrincipal direction.succ point)
            firstField
            (rawDirectionalDerivative centered point direction.succ) := by
    unfold spatialBilinearPrincipalPairing
    dsimp only
    apply Finset.sum_congr rfl
    intro direction _
    rw [rawDirectionalDerivative_centeredField basis basisRegular second point]
  have pairingLaw' :
      diracMatterBilinearFlux
            (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
            firstField
            (matterCoordinateEquiv.symm
              (cauchySafeMatterVolterraVelocity FixedCurrent centered point)) +
          spatialBilinearPrincipalPairing basis first second time space =
        0 := by
    rw [principalEq]
    change
      Complex.re
          (diracExteriorMatterCoordinatePairing firstField
            (diracMatrixMatterAction
              (coframeCoordinateDiracEvolutionPrincipal
                (FixedCurrent.coframe point) 0)
              (matterCoordinateEquiv.symm
                (cauchySafeMatterVolterraVelocity FixedCurrent centered
                  point)))) +
        ∑ direction : Fin 3,
          Complex.re
            (diracExteriorMatterCoordinatePairing firstField
              (diracMatrixMatterAction
                (coframeCoordinateDiracEvolutionPrincipal
                  (FixedCurrent.coframe point) direction.succ)
                (rawDirectionalDerivative centered point direction.succ))) =
        0
    exact pairingLaw
  unfold diracMatterWeakStiffnessDensity fixedWeakConstantStiffnessDensity
  rw [carrierResponseEq, diracExteriorMatterEnergyPairing_add_right]
  change
    -(diracMatterBilinearFlux
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          firstField
          (matterCoordinateEquiv.symm
            (fixedConstantActionResponse time (fiberCoefficient secondField)
              space)) +
        diracMatterBilinearFlux
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          firstField
          (matterCoordinateEquiv.symm
            (cauchySafeMatterVolterraVelocity FixedCurrent centered point))) =
      -diracMatterBilinearFlux
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          firstField
          (matterCoordinateEquiv.symm
            (fixedConstantActionResponse time (fiberCoefficient secondField)
              space)) +
        spatialBilinearPrincipalPairing basis first second time space
  linarith

private theorem fixedSpatialEnergyFlux_fderiv_coordinate_raw
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    let point := diracMatterSpacetimeCoordinatePoint time space
    let field :=
      fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
    let fieldDerivative := rawDirectionalDerivative field point direction.succ
    let coefficientDerivative :=
      fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ time space
    fderiv ℝ
        (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal field time direction)
        space (Pi.single direction 1) =
      2 * Complex.re
          (diracExteriorMatterCoordinatePairing (field point)
            (diracMatrixMatterAction
              (fixedEvolutionPrincipal direction.succ point) fieldDerivative)) +
        Complex.re
          (diracExteriorMatterCoordinatePairing (field point)
            (diracMatrixMatterAction coefficientDerivative (field point))) := by
  dsimp only
  let point := diracMatterSpacetimeCoordinatePoint time space
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  let fieldDerivative := rawDirectionalDerivative field point direction.succ
  let coefficientDerivative :=
    fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ time space
  have curveDerivative := diracMatterEnergyFlux_coordinate_hasDerivAt
    (fun candidateDirection candidatePoint ↦
      fixedEvolutionPrincipal candidateDirection candidatePoint)
    field point direction.succ fieldDerivative
    (diracMatrixMatterAction coefficientDerivative (field point))
    (coframeCoordinateDiracEvolutionPrincipal_isHermitian
      (FixedCurrent.coframe point) direction.succ)
    (fixedWeakSpatialCandidate_internalCoordinate_hasDerivAt basis
      basisRegular coefficient point direction.succ)
    (fixedWeakSpatialCandidate_actedInternalCoordinate_hasDerivAt basis
      basisRegular coefficient time space direction.succ)
  rw [diracMatterSpatialEnergyFlux_fderiv_coordinate
    (fun candidateDirection candidatePoint ↦
      fixedEvolutionPrincipal candidateDirection candidatePoint)
    field time direction space
    ((fixedSpatialEnergyFlux_contDiff_one basis basisRegular coefficient time
      direction).differentiable one_ne_zero space)]
  simpa [point, field, fieldDerivative, coefficientDerivative] using
    curveDerivative.deriv

private theorem fixedSpatialEnergyFlux_fderiv_coordinate
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    let point := diracMatterSpacetimeCoordinatePoint time space
    let field :=
      fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
    let centered := centeredField field point
    fderiv ℝ
        (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal field time direction)
        space (Pi.single direction 1) =
      2 * diracExteriorMatterEnergyPairing
          (fixedEvolutionPrincipal direction.succ point)
          (diracMatterSpatialGalerkinSynthesis basis coefficient space)
          (rawDirectionalDerivative centered point direction.succ) +
        diracMatterWeakMassDensity
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ
            time)
          basis coefficient coefficient space := by
  dsimp only
  let point := diracMatterSpacetimeCoordinatePoint time space
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  let centered := centeredField field point
  rw [fixedSpatialEnergyFlux_fderiv_coordinate_raw basis basisRegular
    coefficient time space direction]
  rw [← rawDirectionalDerivative_centeredField basis basisRegular coefficient
    point direction.succ]
  rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice basis coefficient
    time space]
  rfl

private theorem fixedSpatialBilinearFlux_fderiv_coordinate
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    let point := diracMatterSpacetimeCoordinatePoint time space
    let firstField :=
      fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first
    let secondField :=
      fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second
    fderiv ℝ
        (diracMatterSpatialBilinearFlux fixedEvolutionPrincipal
          firstField secondField time direction)
        space (Pi.single direction 1) =
      diracMatterBilinearFlux
          (fixedEvolutionPrincipal direction.succ point)
          (diracMatterSpatialGalerkinSynthesis basis second space)
          (rawDirectionalDerivative firstField point direction.succ) +
        diracMatterBilinearFlux
          (fixedEvolutionPrincipal direction.succ point)
          (diracMatterSpatialGalerkinSynthesis basis first space)
          (rawDirectionalDerivative secondField point direction.succ) +
        diracMatterWeakMassDensity
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ
            time)
          basis first second space := by
  dsimp only
  let point := diracMatterSpacetimeCoordinatePoint time space
  let firstField :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first
  let secondField :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second
  let firstDerivative :=
    rawDirectionalDerivative firstField point direction.succ
  let secondDerivative :=
    rawDirectionalDerivative secondField point direction.succ
  let coefficientDerivative :=
    fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ time space
  have curveDerivative := diracMatterBilinearFlux_coordinate_hasDerivAt
    fixedEvolutionPrincipal firstField secondField point direction.succ
    firstDerivative secondDerivative
    (diracMatrixMatterAction coefficientDerivative (secondField point))
    (coframeCoordinateDiracEvolutionPrincipal_isHermitian
      (FixedCurrent.coframe point) direction.succ)
    (fixedWeakSpatialCandidate_internalCoordinate_hasDerivAt basis
      basisRegular first point direction.succ)
    (fixedWeakSpatialCandidate_actedInternalCoordinate_hasDerivAt basis
      basisRegular second time space direction.succ)
  rw [diracMatterSpatialBilinearFlux_fderiv_coordinate
    fixedEvolutionPrincipal firstField secondField time direction space
    ((fixedSpatialBilinearFlux_contDiff_one basis basisRegular first second time
      direction).differentiable one_ne_zero space)]
  have firstAt : firstField point =
      diracMatterSpatialGalerkinSynthesis basis first space := by
    exact fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice basis first
      time space
  have secondAt : secondField point =
      diracMatterSpatialGalerkinSynthesis basis second space := by
    exact fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice basis second
      time space
  rw [firstAt, secondAt] at curveDerivative
  simpa [point, firstField, secondField, firstDerivative, secondDerivative,
    coefficientDerivative, diracMatterWeakMassDensity,
    diracExteriorMatterEnergyPairing] using curveDerivative.deriv

private theorem fixedSpatialBilinearFluxDivergence_eq
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialFluxDivergence
        (diracMatterSpatialBilinearFlux fixedEvolutionPrincipal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first)
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second)
          time)
        space =
      spatialBilinearPrincipalPairing basis second first time space +
        spatialBilinearPrincipalPairing basis first second time space +
        ∑ direction : Fin 3,
          diracMatterWeakMassDensity
            (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ
              time)
            basis first second space := by
  unfold diracMatterSpatialFluxDivergence
  simp_rw [fixedSpatialBilinearFlux_fderiv_coordinate basis basisRegular
    first second time space]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  unfold spatialBilinearPrincipalPairing
  dsimp only

private theorem fixedSpatialFluxDivergence_eq
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialFluxDivergence
        (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
          time)
        space =
      2 * spatialPrincipalPairing basis coefficient time space +
        ∑ direction : Fin 3,
          diracMatterWeakMassDensity
            (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ
              time)
            basis coefficient coefficient space := by
  unfold diracMatterSpatialFluxDivergence
  simp_rw [fixedSpatialEnergyFlux_fderiv_coordinate basis basisRegular
    coefficient time space]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

private theorem fixedWeakSpatialCandidate_timeLine
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (point : BasePoint)
    (parameter : ℝ) :
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
        (diracMatterCoordinateLine point canonicalLorentzianTimeDirection
          parameter) =
      fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient point := by
  apply matterCoordinateEquiv.injective
  simp only [fixedP506L0CauchySafeMatterWeakSpatialCandidate,
    cauchySafeMatterGalerkinSynthesis_coordinates]
  apply Finset.sum_congr rfl
  intro mode _
  congr 1
  unfold fixedP506L0CauchySafeMatterWeakSpatialBasisLift
  have projectionTimeDirection :
      canonicalSpatialProjection
          (coordinateDirection canonicalLorentzianTimeDirection) = 0 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [canonicalSpatialProjection, coordinateDirection,
        canonicalLorentzianTimeDirection, localBaseCoordinate_apply]
  rw [diracMatterCoordinateLine, map_add, map_smul,
    projectionTimeDirection, smul_zero, add_zero]

private theorem fixedWeakSpatialCandidate_rawTimeDerivative_zero
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (point : BasePoint) :
    rawDirectionalDerivative
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
        point canonicalLorentzianTimeDirection = 0 := by
  apply (diracExteriorMatterCoordinateFamily_eq_zero_iff _).mp
  intro internal
  funext spin
  have actual := fixedWeakSpatialCandidate_internalCoordinate_hasDerivAt
    basis basisRegular coefficient point canonicalLorentzianTimeDirection
    internal spin
  have constantDerivative : HasDerivAt
      (fun _parameter : ℝ ↦
        internalMatterCoordinate internal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
            point spin))
      0 0 := hasDerivAt_const 0 _
  have lineEq :
      (fun parameter ↦
        internalMatterCoordinate internal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
            (diracMatterCoordinateLine point
              canonicalLorentzianTimeDirection parameter) spin)) =
        fun _parameter : ℝ ↦
          internalMatterCoordinate internal
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
              point spin) := by
    funext parameter
    rw [fixedWeakSpatialCandidate_timeLine]
  rw [lineEq] at actual
  exact actual.unique constantDerivative

private theorem fixedSpatialEnergyDensity_eq_weakMassDensity
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterSpatialEnergyDensity fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient) =
      fun time space ↦
        diracMatterWeakMassDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix time)
          basis coefficient coefficient space := by
  funext time space
  unfold diracMatterSpatialEnergyDensity diracMatterEnergyFlux
  dsimp only
  rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice]
  rfl

private theorem fixedSpatialEnergyDensity_contDiff_one
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    ContDiff ℝ 1
      (Function.uncurry
        (diracMatterSpatialEnergyDensity fixedEvolutionPrincipal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient))) := by
  have joint := diracMatterWeakMassDensity_joint_contDiff_one
    fixedP506L0CauchySafeMatterWeakMassMatrix basis
    (fun row column ↦
      (fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff row column).of_le
        (by norm_num))
    basisRegular coefficient coefficient
  convert joint using 1
  exact congrArg Function.uncurry
    (fixedSpatialEnergyDensity_eq_weakMassDensity basis coefficient)

private theorem fixedTemporalEnergyFluxDerivative_eq
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterTemporalEnergyFluxDerivative fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
        time space =
      diracMatterWeakMassDensity
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection time)
        basis coefficient coefficient space := by
  let point := diracMatterSpacetimeCoordinatePoint time space
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  let fieldDerivative :=
    rawDirectionalDerivative field point canonicalLorentzianTimeDirection
  let coefficientDerivative :=
    fixedEvolutionPrincipalDirectionalDerivativeOnSlice
      canonicalLorentzianTimeDirection time space
  have curveDerivative := diracMatterEnergyFlux_coordinate_hasDerivAt
    (fun candidateDirection candidatePoint ↦
      fixedEvolutionPrincipal candidateDirection candidatePoint)
    field point canonicalLorentzianTimeDirection fieldDerivative
    (diracMatrixMatterAction coefficientDerivative (field point))
    (coframeCoordinateDiracEvolutionPrincipal_isHermitian
      (FixedCurrent.coframe point) canonicalLorentzianTimeDirection)
    (fixedWeakSpatialCandidate_internalCoordinate_hasDerivAt basis
      basisRegular coefficient point canonicalLorentzianTimeDirection)
    (fixedWeakSpatialCandidate_actedInternalCoordinate_hasDerivAt basis
      basisRegular coefficient time space canonicalLorentzianTimeDirection)
  have fieldDerivativeZero : fieldDerivative = 0 := by
    exact fixedWeakSpatialCandidate_rawTimeDerivative_zero basis basisRegular
      coefficient point
  unfold diracMatterTemporalEnergyFluxDerivative
  rw [show field point =
      diracMatterSpatialGalerkinSynthesis basis coefficient space by
    exact fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice basis
      coefficient time space] at curveDerivative
  rw [fieldDerivativeZero] at curveDerivative
  simpa [point, field, fieldDerivative, coefficientDerivative,
    diracMatterWeakMassDensity, diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing] using curveDerivative.deriv

private theorem fixedWeakMassDensity_timeDerivative_eq
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialEnergyTimeDerivative
        (fun candidateTime ↦
          diracMatterWeakMassDensity
            (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
            basis coefficient coefficient)
        time space =
      diracMatterWeakMassDensity
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection time)
        basis coefficient coefficient space := by
  let field :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
  have densityEq :=
    fixedSpatialEnergyDensity_eq_weakMassDensity basis coefficient
  calc
    diracMatterSpatialEnergyTimeDerivative
        (fun candidateTime ↦
          diracMatterWeakMassDensity
            (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
            basis coefficient coefficient)
        time space =
      diracMatterSpatialEnergyTimeDerivative
        (diracMatterSpatialEnergyDensity fixedEvolutionPrincipal field)
        time space := by rw [densityEq]
    _ = diracMatterTemporalEnergyFluxDerivative
        fixedEvolutionPrincipal field time space :=
      diracMatterSpatialEnergyTimeDerivative_eq_temporalEnergyFluxDerivative
        fixedEvolutionPrincipal field
        (fixedSpatialEnergyDensity_contDiff_one basis basisRegular coefficient)
        time space
    _ = _ := fixedTemporalEnergyFluxDerivative_eq basis basisRegular coefficient
      time space

private theorem fixedWeakMassDensity_timeDerivative_bilinear_eq
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialEnergyTimeDerivative
        (fun candidateTime ↦
          diracMatterWeakMassDensity
            (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
            basis first second)
        time space =
      diracMatterWeakMassDensity
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection time)
        basis first second space := by
  let point := diracMatterSpacetimeCoordinatePoint time space
  let firstField :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first
  let secondField :=
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second
  let coefficientDerivative :=
    fixedEvolutionPrincipalDirectionalDerivativeOnSlice
      canonicalLorentzianTimeDirection time space
  have firstDerivativeZero :
      rawDirectionalDerivative firstField point
        canonicalLorentzianTimeDirection = 0 := by
    exact fixedWeakSpatialCandidate_rawTimeDerivative_zero basis basisRegular
      first point
  have secondDerivativeZero :
      rawDirectionalDerivative secondField point
        canonicalLorentzianTimeDirection = 0 := by
    exact fixedWeakSpatialCandidate_rawTimeDerivative_zero basis basisRegular
      second point
  have curveDerivative := diracMatterBilinearFlux_coordinate_hasDerivAt
    fixedEvolutionPrincipal firstField secondField point
    canonicalLorentzianTimeDirection
    (rawDirectionalDerivative firstField point
      canonicalLorentzianTimeDirection)
    (rawDirectionalDerivative secondField point
      canonicalLorentzianTimeDirection)
    (diracMatrixMatterAction coefficientDerivative (secondField point))
    (coframeCoordinateDiracEvolutionPrincipal_isHermitian
      (FixedCurrent.coframe point) canonicalLorentzianTimeDirection)
    (fixedWeakSpatialCandidate_internalCoordinate_hasDerivAt basis
      basisRegular first point canonicalLorentzianTimeDirection)
    (fixedWeakSpatialCandidate_actedInternalCoordinate_hasDerivAt basis
      basisRegular second time space canonicalLorentzianTimeDirection)
  have firstAt : firstField point =
      diracMatterSpatialGalerkinSynthesis basis first space := by
    exact fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice basis first
      time space
  have secondAt : secondField point =
      diracMatterSpatialGalerkinSynthesis basis second space := by
    exact fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice basis second
      time space
  rw [firstDerivativeZero, secondDerivativeZero, firstAt, secondAt] at curveDerivative
  have curveDerivativeValue :
      HasDerivAt
        (fun parameter ↦
          let candidate := diracMatterCoordinateLine point
            canonicalLorentzianTimeDirection parameter
          diracMatterBilinearFlux
            (fixedEvolutionPrincipal canonicalLorentzianTimeDirection candidate)
            (firstField candidate) (secondField candidate))
        (diracMatterWeakMassDensity
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection time)
          basis first second space)
        0 := by
    simpa [coefficientDerivative, diracMatterWeakMassDensity,
      diracExteriorMatterEnergyPairing, diracMatterBilinearFlux,
      diracExteriorMatterCoordinatePairing, dotProduct] using curveDerivative
  have shiftedDerivative : HasDerivAt
      (fun candidateTime ↦
        let candidate := diracMatterCoordinateLine point
          canonicalLorentzianTimeDirection (candidateTime - time)
        diracMatterBilinearFlux
          (fixedEvolutionPrincipal canonicalLorentzianTimeDirection candidate)
          (firstField candidate) (secondField candidate))
      (diracMatterWeakMassDensity
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection time)
        basis first second space)
      time := by
    have atShift : HasDerivAt
        (fun parameter ↦
          let candidate := diracMatterCoordinateLine point
            canonicalLorentzianTimeDirection parameter
          diracMatterBilinearFlux
            (fixedEvolutionPrincipal canonicalLorentzianTimeDirection candidate)
            (firstField candidate) (secondField candidate))
        (diracMatterWeakMassDensity
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection time)
          basis first second space)
        (time - time) := by
      simpa using curveDerivativeValue
    exact HasDerivAt.comp_sub_const time time atShift
  have lineEq (candidateTime : ℝ) :
      diracMatterCoordinateLine point canonicalLorentzianTimeDirection
          (candidateTime - time) =
        diracMatterSpacetimeCoordinatePoint candidateTime space := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [point, diracMatterCoordinateLine,
        diracMatterSpacetimeCoordinatePoint, canonicalCauchySlicePoint,
        canonicalLorentzianTimeDirection, coordinateDirection,
        Fin.sum_univ_three]
  have densityDerivative : HasDerivAt
      (fun candidateTime ↦
        diracMatterWeakMassDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
          basis first second space)
      (diracMatterWeakMassDensity
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection time)
        basis first second space)
      time := by
    convert shiftedDerivative using 1
    funext candidateTime
    rw [lineEq]
    dsimp only [firstField, secondField]
    rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice,
      fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice]
    rfl
  have generatedDerivative :=
    diracMatterSpatialEnergyTimeDerivative_hasDerivAt
      (fun candidateTime ↦
        diracMatterWeakMassDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
          basis first second)
      (diracMatterWeakMassDensity_joint_contDiff_one
        fixedP506L0CauchySafeMatterWeakMassMatrix basis
        (fun row column ↦
          (fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff row column).of_le
            (by norm_num))
        basisRegular first second)
      time space
  exact generatedDerivative.unique densityDerivative

private theorem fixedPointwiseRate_fiberCoefficient
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    fixedPointwiseRate (time, space)
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis coefficient space)) =
      (∑ direction : LorentzianIndex,
        diracMatterWeakMassDensity
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction time)
          basis coefficient coefficient space) -
        2 * diracMatterWeakStiffnessDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix time)
          (fun _mode : Fin 1 ↦
            fun _space : DiracMatterSpatialCoordinates ↦ 1)
          (fixedConstantActionResponse time)
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis coefficient space))
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis coefficient space))
          space := by
  rw [fixedPointwiseRate_eq_formValue]
  unfold fixedPointwiseRateFormValue
  congr 2
  funext direction
  unfold diracMatterWeakMassDensity
  rw [fixedPointwiseConstantSpatialSynthesis]
  simp
  congr 1
  apply matterCoordinateEquiv.injective
  simp [diracMatterSpatialGalerkinSynthesis_coordinates]

private theorem fixedWeakEnergyRateDensity_eq_pointwiseRate_sub_divergence
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialEnergyTimeDerivative
          (fun candidateTime ↦
            diracMatterWeakMassDensity
              (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
              basis coefficient coefficient)
          time space -
        2 * diracMatterWeakStiffnessDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
          (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
          coefficient coefficient space =
      fixedPointwiseRate (time, space)
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis coefficient space)) -
        diracMatterSpatialFluxDivergence
          (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
            time)
          space := by
  rw [fixedWeakMassDensity_timeDerivative_eq basis basisRegular coefficient
    time space]
  rw [fixedWeakStiffnessDensity_eq_constant_add_spatialPrincipal basis
    basisRegular coefficient time space]
  rw [fixedPointwiseRate_fiberCoefficient basis coefficient time space]
  rw [fixedSpatialFluxDivergence_eq basis basisRegular coefficient time space]
  rw [Fin.sum_univ_succ]
  simp only [canonicalLorentzianTimeDirection]
  ring

private theorem fixedWeakStiffnessDensity_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ) :
    Continuous fun space ↦
      diracMatterWeakStiffnessDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
        (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
        coefficient coefficient space := by
  have joint := diracMatterWeakStiffnessDensity_joint_continuous
    fixedP506L0CauchySafeMatterWeakMassMatrix basis
    (fun candidateTime candidateCoefficient candidateSpace ↦
      fixedP506L0CauchySafeMatterWeakActionResponse basis candidateTime
        candidateCoefficient candidateSpace)
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    (fun mode ↦ (basisRegular mode).continuous)
    (fixedP506L0CauchySafeMatterWeakActionResponse_joint_continuous basis
      basisRegular)
    coefficient coefficient
  have timeSlice : Continuous
      (fun space : DiracMatterSpatialCoordinates ↦ (time, space)) :=
    (continuous_const : Continuous
      (fun _space : DiracMatterSpatialCoordinates ↦ time)).prodMk continuous_id
  have restricted := joint.comp timeSlice
  convert restricted using 1
  rfl

private theorem fixedWeakStiffnessDensity_bilinear_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ) :
    Continuous fun space ↦
      diracMatterWeakStiffnessDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
        (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
        first second space := by
  have joint := diracMatterWeakStiffnessDensity_joint_continuous
    fixedP506L0CauchySafeMatterWeakMassMatrix basis
    (fun candidateTime candidateCoefficient candidateSpace ↦
      fixedP506L0CauchySafeMatterWeakActionResponse basis candidateTime
        candidateCoefficient candidateSpace)
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    (fun mode ↦ (basisRegular mode).continuous)
    (fixedP506L0CauchySafeMatterWeakActionResponse_joint_continuous basis
      basisRegular)
    first second
  have timeSlice : Continuous
      (fun space : DiracMatterSpatialCoordinates ↦ (time, space)) :=
    (continuous_const : Continuous
      (fun _space : DiracMatterSpatialCoordinates ↦ time)).prodMk continuous_id
  have restricted := joint.comp timeSlice
  convert restricted using 1
  rfl

private theorem fixedWeakEnergyRateIntegral_box_eq_pointwiseRate
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (hle : a ≤ b)
    (boundaryZero :
      DiracMatterSpatialFluxZeroOnBoxBoundary
        (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
          time)
        a b) :
    (∫ space in Icc a b,
        (diracMatterSpatialEnergyTimeDerivative
            (fun candidateTime ↦
              diracMatterWeakMassDensity
                (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
                basis coefficient coefficient)
            time space -
          2 * diracMatterWeakStiffnessDensity
            (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
            (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
            coefficient coefficient space)) =
      ∫ space in Icc a b,
        fixedPointwiseRate (time, space)
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis coefficient space)) := by
  let flux := diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient) time
  let actualRate : DiracMatterSpatialCoordinates → ℝ := fun space ↦
    diracMatterSpatialEnergyTimeDerivative
        (fun candidateTime ↦
          diracMatterWeakMassDensity
            (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
            basis coefficient coefficient)
        time space -
      2 * diracMatterWeakStiffnessDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
        (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
        coefficient coefficient space
  let pointwiseRate : DiracMatterSpatialCoordinates → ℝ := fun space ↦
    fixedPointwiseRate (time, space)
      (fiberCoefficient
        (diracMatterSpatialGalerkinSynthesis basis coefficient space))
  have fluxRegular : ∀ direction : Fin 3, ContDiff ℝ 1 (flux direction) :=
    fun direction ↦
      fixedSpatialEnergyFlux_contDiff_one basis basisRegular coefficient time
        direction
  have divergenceContinuous : Continuous
      (diracMatterSpatialFluxDivergence flux) :=
    diracMatterSpatialFluxDivergence_continuous flux fluxRegular
  let density : ℝ → DiracMatterSpatialCoordinates → ℝ :=
    fun candidateTime ↦
      diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
        basis coefficient coefficient
  have densityC1 : ContDiff ℝ 1 (Function.uncurry density) := by
    exact diracMatterWeakMassDensity_joint_contDiff_one
      fixedP506L0CauchySafeMatterWeakMassMatrix basis
      (fun row column ↦
        (fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff row column
          ).of_le (by norm_num))
      basisRegular coefficient coefficient
  have temporalContinuous : Continuous fun space ↦
      diracMatterSpatialEnergyTimeDerivative density time space :=
    diracMatterSpatialEnergyTimeDerivative_continuous density densityC1 time
  have actualRateContinuous : Continuous actualRate := by
    exact temporalContinuous.sub
      (continuous_const.mul
        (fixedWeakStiffnessDensity_continuous basis basisRegular coefficient
          time))
  have rateEq : pointwiseRate =
      fun space ↦ actualRate space +
        diracMatterSpatialFluxDivergence flux space := by
    funext space
    have identity :=
      fixedWeakEnergyRateDensity_eq_pointwiseRate_sub_divergence basis
        basisRegular coefficient time space
    dsimp only [actualRate, pointwiseRate, flux]
    linarith
  have pointwiseRateContinuous : Continuous pointwiseRate := by
    rw [rateEq]
    exact actualRateContinuous.add divergenceContinuous
  have pointwiseRateIntegrable : IntegrableOn pointwiseRate (Icc a b) :=
    pointwiseRateContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have divergenceIntegrable : IntegrableOn
      (diracMatterSpatialFluxDivergence flux) (Icc a b) :=
    divergenceContinuous.continuousOn.integrableOn_compact isCompact_Icc
  calc
    (∫ space in Icc a b, actualRate space) =
        ∫ space in Icc a b,
          (pointwiseRate space -
            diracMatterSpatialFluxDivergence flux space) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro space _
      have identity :=
        fixedWeakEnergyRateDensity_eq_pointwiseRate_sub_divergence basis
          basisRegular coefficient time space
      exact identity
    _ = (∫ space in Icc a b, pointwiseRate space) -
        ∫ space in Icc a b,
          diracMatterSpatialFluxDivergence flux space := by
      rw [integral_sub pointwiseRateIntegrable divergenceIntegrable]
    _ = ∫ space in Icc a b, pointwiseRate space := by
      rw [integral_diracMatterSpatialFluxDivergence_box_eq_zero flux a b hle
        fluxRegular boundaryZero, sub_zero]

private def fixedWeakTemporalEnergyDensity
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) (space : DiracMatterSpatialCoordinates) : ℝ :=
  diracMatterSpatialEnergyTimeDerivative
      (fun candidateTime ↦
        diracMatterWeakMassDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
          basis coefficient coefficient)
      time space

private def fixedWeakStiffnessEnergyDensity
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) (space : DiracMatterSpatialCoordinates) : ℝ :=
  diracMatterWeakStiffnessDensity
    (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
    (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
    coefficient coefficient space

private def fixedWeakEnergyRateDensity
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) (space : DiracMatterSpatialCoordinates) : ℝ :=
  fixedWeakTemporalEnergyDensity basis coefficient time space -
    2 * fixedWeakStiffnessEnergyDensity basis coefficient time space

private def fixedWeakEnergyDensity
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) (space : DiracMatterSpatialCoordinates) : ℝ :=
  diracMatterWeakMassDensity
    (fixedP506L0CauchySafeMatterWeakMassMatrix time)
    basis coefficient coefficient space

private def fixedWeakTestGreenRateDensity
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (trial test : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  diracMatterWeakMassDensity
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection time)
      basis trial test space -
    fixedWeakConstantStiffnessDensity basis test trial time space +
    spatialBilinearPrincipalPairing basis trial test time space +
    ∑ direction : Fin 3,
      diracMatterWeakMassDensity
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ time)
        basis test trial space

private def fixedOneModeSpatialBasis
    (_mode : Fin 1) (_space : DiracMatterSpatialCoordinates) : ℝ := 1

private theorem fixedOneModeSpatialBasis_continuous (mode : Fin 1) :
    Continuous (fixedOneModeSpatialBasis mode) :=
  continuous_const

private def fixedOneModeMassInnerLinear
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first : DiracMatterGalerkinCoefficient 1) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ] ℝ where
  toFun second :=
    diracMatterWeakMassDensity (matrix time) fixedOneModeSpatialBasis
      first second space
  map_add' second third := congrFun
    (diracMatterWeakMassDensity_add_right (matrix time)
      fixedOneModeSpatialBasis first second third) space
  map_smul' parameter second := by
    simpa using congrFun
      (diracMatterWeakMassDensity_real_smul_right (matrix time)
        fixedOneModeSpatialBasis parameter first second) space

private def fixedOneModeMassInnerCLM
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first : DiracMatterGalerkinCoefficient 1) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ :=
  ⟨fixedOneModeMassInnerLinear matrix time space first,
    (fixedOneModeMassInnerLinear matrix time space first
      ).continuous_of_finiteDimensional⟩

private def fixedOneModeMassFormLinear
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ]
      (DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ) where
  toFun := fixedOneModeMassInnerCLM matrix time space
  map_add' first second := by
    ext third
    exact congrFun
      (diracMatterWeakMassDensity_add_left (matrix time)
        fixedOneModeSpatialBasis first second third) space
  map_smul' parameter first := by
    ext second
    change diracMatterWeakMassDensity (matrix time) fixedOneModeSpatialBasis
      (parameter • first) second space =
        parameter • diracMatterWeakMassDensity (matrix time)
          fixedOneModeSpatialBasis first second space
    simpa using congrFun
      (diracMatterWeakMassDensity_real_smul_left (matrix time)
        fixedOneModeSpatialBasis parameter first second) space

private def fixedOneModeMassForm
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ]
      (DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ) :=
  ⟨fixedOneModeMassFormLinear matrix time space,
    (fixedOneModeMassFormLinear matrix time space
      ).continuous_of_finiteDimensional⟩

@[simp] private theorem fixedOneModeMassForm_apply
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first second : DiracMatterGalerkinCoefficient 1) :
    fixedOneModeMassForm matrix time space first second =
      diracMatterWeakMassDensity (matrix time) fixedOneModeSpatialBasis
        first second space :=
  rfl

private theorem fixedOneModeMassForm_continuous
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (matrixContinuous : ∀ row column, Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column) :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedOneModeMassForm matrix input.1 input.2) := by
  rw [continuous_clm_apply]
  intro first
  rw [continuous_clm_apply]
  intro second
  exact diracMatterWeakMassDensity_joint_continuous matrix
    fixedOneModeSpatialBasis matrixContinuous
    fixedOneModeSpatialBasis_continuous first second

private def fixedOneModeStiffnessInnerLinear
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first : DiracMatterGalerkinCoefficient 1) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ] ℝ where
  toFun second :=
    diracMatterWeakStiffnessDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      fixedOneModeSpatialBasis (fixedConstantActionResponse time)
      first second space
  map_add' second third := congrFun
    (diracMatterWeakStiffnessDensity_add_right
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      fixedOneModeSpatialBasis (fixedConstantActionResponse time)
      (fixedConstantActionResponse_add time) first second third) space
  map_smul' parameter second := by
    simpa using congrFun
      (diracMatterWeakStiffnessDensity_real_smul_right
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        fixedOneModeSpatialBasis (fixedConstantActionResponse time)
        (fixedConstantActionResponse_real_smul time) parameter first second) space

private def fixedOneModeStiffnessInnerCLM
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first : DiracMatterGalerkinCoefficient 1) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ :=
  ⟨fixedOneModeStiffnessInnerLinear time space first,
    (fixedOneModeStiffnessInnerLinear time space first
      ).continuous_of_finiteDimensional⟩

private def fixedOneModeStiffnessFormLinear
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 →ₗ[ℝ]
      (DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ) where
  toFun := fixedOneModeStiffnessInnerCLM time space
  map_add' first second := by
    ext third
    exact congrFun
      (diracMatterWeakStiffnessDensity_add_left
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        fixedOneModeSpatialBasis (fixedConstantActionResponse time)
        first second third) space
  map_smul' parameter first := by
    ext second
    change diracMatterWeakStiffnessDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      fixedOneModeSpatialBasis (fixedConstantActionResponse time)
      (parameter • first) second space =
        parameter • diracMatterWeakStiffnessDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix time)
          fixedOneModeSpatialBasis (fixedConstantActionResponse time)
          first second space
    exact congrFun
      (diracMatterWeakStiffnessDensity_real_smul_left
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        fixedOneModeSpatialBasis (fixedConstantActionResponse time)
        parameter first second) space

private def fixedOneModeStiffnessForm
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 →L[ℝ]
      (DiracMatterGalerkinCoefficient 1 →L[ℝ] ℝ) :=
  ⟨fixedOneModeStiffnessFormLinear time space,
    (fixedOneModeStiffnessFormLinear time space
      ).continuous_of_finiteDimensional⟩

@[simp] private theorem fixedOneModeStiffnessForm_apply
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first second : DiracMatterGalerkinCoefficient 1) :
    fixedOneModeStiffnessForm time space first second =
      diracMatterWeakStiffnessDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        fixedOneModeSpatialBasis (fixedConstantActionResponse time)
        first second space :=
  rfl

private theorem fixedOneModeStiffnessForm_continuous :
    Continuous (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedOneModeStiffnessForm input.1 input.2) := by
  rw [continuous_clm_apply]
  intro first
  rw [continuous_clm_apply]
  intro second
  exact diracMatterWeakStiffnessDensity_joint_continuous
    fixedP506L0CauchySafeMatterWeakMassMatrix fixedOneModeSpatialBasis
    fixedConstantActionResponse
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    fixedOneModeSpatialBasis_continuous
    fixedConstantActionResponse_joint_continuous first second

theorem fixedOneModeMassForm_fiberCoefficient
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first second : DiracExteriorMatterCarrier) :
    fixedOneModeMassForm matrix time space (fiberCoefficient first)
        (fiberCoefficient second) =
      diracExteriorMatterEnergyPairing (matrix time space) first second := by
  rw [fixedOneModeMassForm_apply]
  unfold diracMatterWeakMassDensity
  have firstSynthesis :
      diracMatterSpatialGalerkinSynthesis fixedOneModeSpatialBasis
          (fiberCoefficient first) space = first := by
    unfold fixedOneModeSpatialBasis
    exact constantSpatialSynthesis_fiberCoefficient first space
  have secondSynthesis :
      diracMatterSpatialGalerkinSynthesis fixedOneModeSpatialBasis
          (fiberCoefficient second) space = second := by
    unfold fixedOneModeSpatialBasis
    exact constantSpatialSynthesis_fiberCoefficient second space
  rw [firstSynthesis, secondSynthesis]

theorem fixedOneModeStiffnessForm_fiberCoefficient
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (first second : DiracExteriorMatterCarrier) :
    fixedOneModeStiffnessForm time space (fiberCoefficient first)
        (fiberCoefficient second) =
      -diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space) first
        (matterCoordinateEquiv.symm
          (fixedConstantActionResponse time (fiberCoefficient second) space)) := by
  rw [fixedOneModeStiffnessForm_apply]
  unfold diracMatterWeakStiffnessDensity
  have firstSynthesis :
      diracMatterSpatialGalerkinSynthesis fixedOneModeSpatialBasis
          (fiberCoefficient first) space = first := by
    unfold fixedOneModeSpatialBasis
    exact constantSpatialSynthesis_fiberCoefficient first space
  rw [firstSynthesis]

private def fixedWeakTestValueCoefficient
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 :=
  fiberCoefficientCLM
    (testCoordinates
      (diracMatterSpacetimeCoordinatePoint point.1 point.2))

private def fixedWeakTestSpatialDerivativeCoefficient
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates)
    (direction : Fin 3) : DiracMatterGalerkinCoefficient 1 :=
  fiberCoefficientCLM
    (fieldDirectionalDerivative testCoordinates
      (diracMatterSpacetimeCoordinatePoint point.1 point.2) direction.succ)

private def fixedWeakTestPointwiseGreenRate
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates)
    (trial : DiracMatterGalerkinCoefficient 1) : ℝ :=
  fixedOneModeMassForm
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection)
      point.1 point.2 trial (fixedWeakTestValueCoefficient testCoordinates point) -
    fixedOneModeStiffnessForm point.1 point.2
      (fixedWeakTestValueCoefficient testCoordinates point) trial +
    ∑ direction : Fin 3,
      fixedOneModeMassForm (fixedEvolutionPrincipalOnSlice direction.succ)
        point.1 point.2 trial
        (fixedWeakTestSpatialDerivativeCoefficient testCoordinates point
          direction) +
    ∑ direction : Fin 3,
      fixedOneModeMassForm
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ)
        point.1 point.2 (fixedWeakTestValueCoefficient testCoordinates point)
        trial

private theorem fixedWeakTestValueCoefficient_continuous
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates) :
    Continuous (fixedWeakTestValueCoefficient testCoordinates) := by
  unfold fixedWeakTestValueCoefficient
  exact fiberCoefficientCLM.continuous.comp
    (testRegular.continuous.comp
      diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous)

private def fixedWeakTestPointwiseMassPairing
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates)
    (trial : DiracMatterGalerkinCoefficient 1) : ℝ :=
  fixedOneModeMassForm fixedP506L0CauchySafeMatterWeakMassMatrix
    point.1 point.2 trial (fixedWeakTestValueCoefficient testCoordinates point)

private theorem fixedWeakTestPointwiseMassPairing_joint_continuous
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates) :
    Continuous (fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
      fixedWeakTestPointwiseMassPairing testCoordinates input.1 input.2) := by
  exact
    ((fixedOneModeMassForm_continuous
        fixedP506L0CauchySafeMatterWeakMassMatrix
        fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
      ).comp continuous_fst).clm_apply continuous_snd |>.clm_apply
      ((fixedWeakTestValueCoefficient_continuous testCoordinates testRegular
        ).comp continuous_fst)

private theorem fixedWeakTestPointwiseMassPairing_real_smul
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (trial : DiracMatterGalerkinCoefficient 1) :
    fixedWeakTestPointwiseMassPairing testCoordinates point
        (parameter • trial) =
      parameter * fixedWeakTestPointwiseMassPairing testCoordinates point
        trial := by
  unfold fixedWeakTestPointwiseMassPairing
  simp

private theorem fixedWeakTestSpatialDerivativeCoefficient_continuous
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (direction : Fin 3) :
    Continuous (fun point ↦
      fixedWeakTestSpatialDerivativeCoefficient testCoordinates point
        direction) := by
  unfold fixedWeakTestSpatialDerivativeCoefficient
  have derivativeContinuous : Continuous (fun point : BasePoint ↦
      fieldDirectionalDerivative testCoordinates point direction.succ) := by
    unfold fieldDirectionalDerivative
    exact (testRegular.continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  exact fiberCoefficientCLM.continuous.comp
    (derivativeContinuous.comp
      diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous)

private theorem fixedWeakTestPointwiseGreenRate_joint_continuous
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates) :
    Continuous (fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
      fixedWeakTestPointwiseGreenRate testCoordinates input.1 input.2) := by
  have testValueContinuous :=
    fixedWeakTestValueCoefficient_continuous testCoordinates testRegular
  have temporalMassFormContinuous := fixedOneModeMassForm_continuous
    (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
      canonicalLorentzianTimeDirection)
    (fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
      canonicalLorentzianTimeDirection)
  have temporalTermContinuous : Continuous (fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
      fixedOneModeMassForm
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection)
        input.1.1 input.1.2 input.2
        (fixedWeakTestValueCoefficient testCoordinates input.1)) :=
    ((temporalMassFormContinuous.comp continuous_fst).clm_apply
      continuous_snd).clm_apply (testValueContinuous.comp continuous_fst)
  have stiffnessTermContinuous : Continuous (fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
      fixedOneModeStiffnessForm input.1.1 input.1.2
        (fixedWeakTestValueCoefficient testCoordinates input.1) input.2) :=
    ((fixedOneModeStiffnessForm_continuous.comp continuous_fst).clm_apply
      (testValueContinuous.comp continuous_fst)).clm_apply continuous_snd
  have principalTermContinuous (direction : Fin 3) : Continuous (fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
      fixedOneModeMassForm (fixedEvolutionPrincipalOnSlice direction.succ)
        input.1.1 input.1.2 input.2
        (fixedWeakTestSpatialDerivativeCoefficient testCoordinates input.1
          direction)) := by
    have formContinuous := fixedOneModeMassForm_continuous
      (fixedEvolutionPrincipalOnSlice direction.succ)
      (fun row column ↦
        (fixedEvolutionPrincipalOnSlice_entry_contDiff direction.succ row column
          ).continuous)
    exact ((formContinuous.comp continuous_fst).clm_apply continuous_snd
      ).clm_apply
        ((fixedWeakTestSpatialDerivativeCoefficient_continuous testCoordinates
          testRegular direction).comp continuous_fst)
  have derivativeTermContinuous (direction : Fin 3) : Continuous (fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
      fixedOneModeMassForm
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ)
        input.1.1 input.1.2
        (fixedWeakTestValueCoefficient testCoordinates input.1) input.2) := by
    have formContinuous := fixedOneModeMassForm_continuous
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ)
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
        direction.succ)
    exact ((formContinuous.comp continuous_fst).clm_apply
      (testValueContinuous.comp continuous_fst)).clm_apply continuous_snd
  unfold fixedWeakTestPointwiseGreenRate
  convert
    ((temporalTermContinuous.sub stiffnessTermContinuous).add
      ((continuous_finsetSum Finset.univ fun direction _ ↦
        principalTermContinuous direction).add
        (continuous_finsetSum Finset.univ fun direction _ ↦
          derivativeTermContinuous direction))) using 1
  funext input
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

private theorem fixedWeakTestPointwiseGreenRate_real_smul
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (trial : DiracMatterGalerkinCoefficient 1) :
    fixedWeakTestPointwiseGreenRate testCoordinates point
        (parameter • trial) =
      parameter * fixedWeakTestPointwiseGreenRate testCoordinates point trial := by
  unfold fixedWeakTestPointwiseGreenRate
  simp only [map_smul, smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

private theorem fixedWeakTestValueCoefficient_eq
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (test : DiracMatterGalerkinCoefficient candidateModeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (point : ℝ × DiracMatterSpatialCoordinates) :
    fixedWeakTestValueCoefficient testCoordinates point =
      fiberCoefficient
        (diracMatterSpatialGalerkinSynthesis basis test point.2) := by
  rw [testRepresentation]
  unfold fixedWeakTestValueCoefficient
  change fiberCoefficientCLM
      (matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test
          (diracMatterSpacetimeCoordinatePoint point.1 point.2))) = _
  rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice]
  exact (fiberCoefficient_eq_clm _).symm

private theorem exists_fixedWeakTestPointwiseMassPairingBoundOnBox
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ point ∈ Icc timeStart timeEnd ×ˢ Icc a b,
        ∀ trial : DiracMatterGalerkinCoefficient 1,
          ‖fixedWeakTestPointwiseMassPairing testCoordinates point trial‖ ≤
            C * ‖trial‖ := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have carrierNonempty : carrier.Nonempty := by
    exact ⟨(timeStart, a), ⟨left_mem_Icc.mpr timeOrder,
      left_mem_Icc.mpr boxOrder⟩⟩
  exact exists_modeUniformLinearRateBound carrier carrierCompact
    carrierNonempty (fixedWeakTestPointwiseMassPairing testCoordinates)
    (fixedWeakTestPointwiseMassPairing_joint_continuous testCoordinates
      testRegular)
    (fixedWeakTestPointwiseMassPairing_real_smul testCoordinates)

private theorem fixedWeakMassDensity_eq_pointwiseMassPairing
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (trial test : DiracMatterGalerkinCoefficient candidateModeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        basis trial test space =
      fixedWeakTestPointwiseMassPairing testCoordinates (time, space)
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis trial space)) := by
  unfold fixedWeakTestPointwiseMassPairing
  rw [fixedWeakTestValueCoefficient_eq basis test testCoordinates
    testRepresentation (time, space)]
  rw [fixedOneModeMassForm_fiberCoefficient]
  rfl

private theorem fixedWeakMassDensity_norm_le_of_pointwiseMassPairingBound
    {candidateModeCount : ℕ}
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (trial test : DiracMatterGalerkinCoefficient candidateModeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (pointwiseBound :
      ‖fixedWeakTestPointwiseMassPairing testCoordinates (time, space)
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis trial space))‖ ≤
        C * ‖fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis trial space)‖) :
    ‖diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        basis trial test space‖ ≤
      C * (‖matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis trial space)‖ ^ 2 + 1) := by
  let fieldNorm := ‖matterCoordinateEquiv
    (diracMatterSpatialGalerkinSynthesis basis trial space)‖
  have normLeSquareAddOne : fieldNorm ≤ fieldNorm ^ 2 + 1 := by
    nlinarith [sq_nonneg (fieldNorm - 1 / 2)]
  calc
    ‖diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time)
        basis trial test space‖ =
        ‖fixedWeakTestPointwiseMassPairing testCoordinates (time, space)
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis trial space))‖ := by
      rw [fixedWeakMassDensity_eq_pointwiseMassPairing basis trial test
        testCoordinates testRepresentation time space]
    _ ≤ C * ‖fiberCoefficient
        (diracMatterSpatialGalerkinSynthesis basis trial space)‖ :=
      pointwiseBound
    _ = C * fieldNorm := by rw [fiberCoefficient_norm]
    _ ≤ C * (fieldNorm ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left normLeSquareAddOne CNonnegative

private theorem fixedWeakTestSpatialDerivativeCoefficient_eq
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (test : DiracMatterGalerkinCoefficient candidateModeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (point : ℝ × DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    fixedWeakTestSpatialDerivativeCoefficient testCoordinates point direction =
      fiberCoefficient
        (rawDirectionalDerivative
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test)
          (diracMatterSpacetimeCoordinatePoint point.1 point.2)
          direction.succ) := by
  rw [testRepresentation]
  unfold fixedWeakTestSpatialDerivativeCoefficient rawDirectionalDerivative
  rw [fiberCoefficient_eq_clm, matterCoordinateEquiv.apply_symm_apply]

private theorem fixedWeakTestGreenRateDensity_eq_pointwise
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (trial test : DiracMatterGalerkinCoefficient candidateModeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (time : ℝ) (space : DiracMatterSpatialCoordinates) :
    fixedWeakTestGreenRateDensity basis trial test time space =
      fixedWeakTestPointwiseGreenRate testCoordinates (time, space)
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis trial space)) := by
  let point := diracMatterSpacetimeCoordinatePoint time space
  let trialField := diracMatterSpatialGalerkinSynthesis basis trial space
  let testField := diracMatterSpatialGalerkinSynthesis basis test space
  have testValueEq := fixedWeakTestValueCoefficient_eq basis test
    testCoordinates testRepresentation (time, space)
  have testDerivativeEq (direction : Fin 3) :=
    fixedWeakTestSpatialDerivativeCoefficient_eq basis test testCoordinates
      testRepresentation (time, space) direction
  unfold fixedWeakTestPointwiseGreenRate
  rw [testValueEq]
  simp_rw [testDerivativeEq]
  simp_rw [fixedOneModeMassForm_fiberCoefficient]
  rw [fixedOneModeStiffnessForm_fiberCoefficient]
  unfold fixedWeakTestGreenRateDensity fixedWeakConstantStiffnessDensity
    spatialBilinearPrincipalPairing diracMatterWeakMassDensity
  dsimp only
  rfl

private theorem exists_fixedWeakTestPointwiseGreenRateBoundOnBox
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ point ∈ Icc timeStart timeEnd ×ˢ Icc a b,
        ∀ trial : DiracMatterGalerkinCoefficient 1,
          ‖fixedWeakTestPointwiseGreenRate testCoordinates point trial‖ ≤
            C * ‖trial‖ := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have carrierNonempty : carrier.Nonempty := by
    exact ⟨(timeStart, a), ⟨left_mem_Icc.mpr timeOrder,
      left_mem_Icc.mpr boxOrder⟩⟩
  exact exists_modeUniformLinearRateBound carrier carrierCompact
    carrierNonempty (fixedWeakTestPointwiseGreenRate testCoordinates)
    (fixedWeakTestPointwiseGreenRate_joint_continuous testCoordinates
      testRegular)
    (fixedWeakTestPointwiseGreenRate_real_smul testCoordinates)

private theorem fixedWeakTestGreenRateDensity_norm_le
    {candidateModeCount : ℕ}
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (trial test : DiracMatterGalerkinCoefficient candidateModeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (time : ℝ) (space : DiracMatterSpatialCoordinates)
    (pointwiseBound :
      ‖fixedWeakTestPointwiseGreenRate testCoordinates (time, space)
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis trial space))‖ ≤
        C * ‖fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis trial space)‖) :
    ‖fixedWeakTestGreenRateDensity basis trial test time space‖ ≤
      C *
        (‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis trial space)‖ ^ 2 + 1) := by
  let fieldNorm := ‖matterCoordinateEquiv
    (diracMatterSpatialGalerkinSynthesis basis trial space)‖
  have normLeSquareAddOne : fieldNorm ≤ fieldNorm ^ 2 + 1 := by
    nlinarith [sq_nonneg (fieldNorm - 1 / 2)]
  calc
    ‖fixedWeakTestGreenRateDensity basis trial test time space‖ =
        ‖fixedWeakTestPointwiseGreenRate testCoordinates (time, space)
          (fiberCoefficient
            (diracMatterSpatialGalerkinSynthesis basis trial space))‖ := by
      rw [fixedWeakTestGreenRateDensity_eq_pointwise basis trial test
        testCoordinates testRepresentation time space]
    _ ≤ C * ‖fiberCoefficient
        (diracMatterSpatialGalerkinSynthesis basis trial space)‖ :=
      pointwiseBound
    _ = C * fieldNorm := by
      rw [fiberCoefficient_norm]
    _ ≤ C * (fieldNorm ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left normLeSquareAddOne CNonnegative

private def fixedLocalCoefficient
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (space : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient 1 :=
  fiberCoefficient (diracMatterSpatialGalerkinSynthesis basis coefficient space)

private def fixedWeakPointwiseRateDensity
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) (space : DiracMatterSpatialCoordinates) : ℝ :=
  fixedPointwiseRate (time, space)
    (fixedLocalCoefficient basis coefficient space)

private def fixedWeakPointwiseEnergyDensity
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) (space : DiracMatterSpatialCoordinates) : ℝ :=
  fixedPointwiseEnergy (time, space)
    (fixedLocalCoefficient basis coefficient space)

private theorem fixedLocalCoefficient_continuous
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount) :
    Continuous (fixedLocalCoefficient basis coefficient) := by
  let coordinatePath := fun space ↦ matterCoordinateEquiv
    (diracMatterSpatialGalerkinSynthesis basis coefficient space)
  have coordinatePathContinuous : Continuous coordinatePath :=
    diracMatterSpatialGalerkinSynthesis_coordinates_continuous basis
      basisContinuous coefficient
  have composed : Continuous (fiberCoefficientCLM ∘ coordinatePath) :=
    fiberCoefficientCLM.continuous.comp coordinatePathContinuous
  convert composed using 1
  funext space
  rfl

private theorem fixedWeakPointwiseRateDensity_continuous
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) :
    Continuous (fixedWeakPointwiseRateDensity basis coefficient time) := by
  let inputPath := fun space : DiracMatterSpatialCoordinates ↦
    ((time, space), fixedLocalCoefficient basis coefficient space)
  have inputPathContinuous : Continuous inputPath :=
    (continuous_const.prodMk continuous_id).prodMk
      (fixedLocalCoefficient_continuous basis basisContinuous coefficient)
  have composed := fixedPointwiseRate_joint_continuous.comp inputPathContinuous
  convert composed using 1
  funext space
  rfl

private theorem fixedWeakPointwiseEnergyDensity_continuous
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) :
    Continuous (fixedWeakPointwiseEnergyDensity basis coefficient time) := by
  let inputPath := fun space : DiracMatterSpatialCoordinates ↦
    ((time, space), fixedLocalCoefficient basis coefficient space)
  have inputPathContinuous : Continuous inputPath :=
    (continuous_const.prodMk continuous_id).prodMk
      (fixedLocalCoefficient_continuous basis basisContinuous coefficient)
  have composed := fixedPointwiseEnergy_joint_continuous.comp inputPathContinuous
  convert composed using 1
  funext space
  rfl

private theorem fixedWeakEnergyCoercivityOnBox_of_pointwiseBound
    {candidateModeCount : ℕ}
    (κ : ℝ)
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (pointwiseBound : ∀ space ∈ Icc a b,
      κ * ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis coefficient space)‖ ^ 2 ≤
        fixedWeakPointwiseEnergyDensity basis coefficient time space) :
    κ * ∫ space in Icc a b,
        ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis coefficient space)‖ ^ 2 ≤
      ∫ space in Icc a b,
        fixedWeakEnergyDensity basis coefficient time space := by
  let coordinatePath := fun space ↦ matterCoordinateEquiv
    (diracMatterSpatialGalerkinSynthesis basis coefficient space)
  have coordinatePathContinuous : Continuous coordinatePath :=
    diracMatterSpatialGalerkinSynthesis_coordinates_continuous basis
      basisContinuous coefficient
  have normSquareContinuous : Continuous (fun space ↦
      ‖matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis coefficient space)‖ ^ 2) := by
    exact coordinatePathContinuous.norm.pow 2
  have normSquareIntegrable : IntegrableOn (fun space ↦
      ‖matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis coefficient space)‖ ^ 2)
      (Icc a b) :=
    normSquareContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have scaledNormSquareIntegrable : IntegrableOn (fun space ↦
      κ * ‖matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis coefficient space)‖ ^ 2)
      (Icc a b) :=
    normSquareIntegrable.const_mul κ
  have energyContinuous := fixedWeakPointwiseEnergyDensity_continuous basis
    basisContinuous coefficient time
  have energyIntegrable : IntegrableOn
      (fixedWeakPointwiseEnergyDensity basis coefficient time) (Icc a b) :=
    energyContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have pointwiseBoundAE : ∀ᵐ space ∂volume.restrict (Icc a b),
      κ * ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis coefficient space)‖ ^ 2 ≤
        fixedWeakPointwiseEnergyDensity basis coefficient time space := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
    exact pointwiseBound space spaceMem
  have energyIntegralEq :
      (∫ space in Icc a b,
          fixedWeakPointwiseEnergyDensity basis coefficient time space) =
        ∫ space in Icc a b,
          fixedWeakEnergyDensity basis coefficient time space := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro space _
    exact fixedPointwiseEnergy_fiberCoefficient basis coefficient time space
  calc
    κ * ∫ space in Icc a b,
        ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis coefficient space)‖ ^ 2 =
        ∫ space in Icc a b,
          κ * ‖matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis basis coefficient space)‖ ^ 2 := by
      rw [integral_const_mul]
    _ ≤ ∫ space in Icc a b,
        fixedWeakPointwiseEnergyDensity basis coefficient time space :=
      integral_mono_ae scaledNormSquareIntegrable energyIntegrable
        pointwiseBoundAE
    _ = ∫ space in Icc a b,
        fixedWeakEnergyDensity basis coefficient time space := energyIntegralEq

private theorem fixedWeakEnergyRateIntegral_box_eq_pointwiseRateDensity
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (boundaryZero :
      DiracMatterSpatialFluxZeroOnBoxBoundary
        (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
          time)
        a b) :
    (∫ space in Icc a b,
        fixedWeakEnergyRateDensity basis coefficient time space) =
      ∫ space in Icc a b,
        fixedWeakPointwiseRateDensity basis coefficient time space := by
  exact fixedWeakEnergyRateIntegral_box_eq_pointwiseRate basis basisRegular
    coefficient time a b boxOrder boundaryZero

private theorem fixedWeakEnergyRateBoundOnBox_of_pointwiseBound
    {candidateModeCount : ℕ}
    (K : ℝ)
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (boundaryZero :
      DiracMatterSpatialFluxZeroOnBoxBoundary
        (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
          time)
        a b)
    (pointwiseBound : ∀ space ∈ Icc a b,
      ‖fixedWeakPointwiseRateDensity basis coefficient time space‖ ≤
        K * fixedWeakPointwiseEnergyDensity basis coefficient time space) :
    ‖∫ space in Icc a b,
        fixedWeakEnergyRateDensity basis coefficient time space‖ ≤
      K * ∫ space in Icc a b,
        fixedWeakEnergyDensity basis coefficient time space := by
  have rateContinuous := fixedWeakPointwiseRateDensity_continuous basis
    (fun mode ↦ (basisRegular mode).continuous) coefficient time
  have energyContinuous := fixedWeakPointwiseEnergyDensity_continuous basis
    (fun mode ↦ (basisRegular mode).continuous) coefficient time
  have rateIntegrable : IntegrableOn
      (fixedWeakPointwiseRateDensity basis coefficient time) (Icc a b) :=
    rateContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have energyIntegrable : IntegrableOn
      (fixedWeakPointwiseEnergyDensity basis coefficient time) (Icc a b) :=
    energyContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have scaledEnergyIntegrable : IntegrableOn
      (fun space ↦ K * fixedWeakPointwiseEnergyDensity basis coefficient time
        space)
      (Icc a b) := energyIntegrable.const_mul K
  have pointwiseBoundAE : ∀ᵐ space ∂volume.restrict (Icc a b),
      ‖fixedWeakPointwiseRateDensity basis coefficient time space‖ ≤
        K * fixedWeakPointwiseEnergyDensity basis coefficient time space := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
    exact pointwiseBound space spaceMem
  have rateIntegralEq :=
    fixedWeakEnergyRateIntegral_box_eq_pointwiseRateDensity basis basisRegular
      coefficient time a b boxOrder boundaryZero
  have energyIntegralEq :
      (∫ space in Icc a b,
          fixedWeakPointwiseEnergyDensity basis coefficient time space) =
        ∫ space in Icc a b,
          fixedWeakEnergyDensity basis coefficient time space := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro space _
    exact fixedPointwiseEnergy_fiberCoefficient basis coefficient time space
  calc
    ‖∫ space in Icc a b,
        fixedWeakEnergyRateDensity basis coefficient time space‖ =
        ‖∫ space in Icc a b,
          fixedWeakPointwiseRateDensity basis coefficient time space‖ := by
      rw [rateIntegralEq]
    _ ≤ ∫ space in Icc a b,
        ‖fixedWeakPointwiseRateDensity basis coefficient time space‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ space in Icc a b,
        K * fixedWeakPointwiseEnergyDensity basis coefficient time space :=
      integral_mono_ae rateIntegrable.norm scaledEnergyIntegrable
        pointwiseBoundAE
    _ = K * ∫ space in Icc a b,
        fixedWeakPointwiseEnergyDensity basis coefficient time space := by
      rw [integral_const_mul]
    _ = K * ∫ space in Icc a b,
        fixedWeakEnergyDensity basis coefficient time space := by
      rw [energyIntegralEq]

private theorem exists_fixedModeUniformWeakEnergyRateBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (_basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
        (time : ℝ),
        time ∈ Icc timeStart timeEnd →
        DiracMatterSpatialFluxZeroOnBoxBoundary
          (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
            time)
          a b →
        ‖∫ space in Icc a b,
            fixedWeakEnergyRateDensity basis coefficient time space‖ ≤
          K * ∫ space in Icc a b,
            fixedWeakEnergyDensity basis coefficient time space := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have carrierNonempty : carrier.Nonempty := by
    exact ⟨(timeStart, a), ⟨⟨le_rfl, timeOrder⟩, ⟨le_rfl, boxOrder⟩⟩⟩
  obtain ⟨K, KNonnegative, pointwiseBound⟩ :=
    exists_fixedModeUniformPointwiseEnergyRateBound carrier carrierCompact
      carrierNonempty
  refine ⟨K, KNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular coefficient time timeMem
    boundaryZero
  apply fixedWeakEnergyRateBoundOnBox_of_pointwiseBound K basis basisRegular
    coefficient time a b boxOrder boundaryZero
  intro space spaceMem
  exact pointwiseBound (time, space) ⟨timeMem, spaceMem⟩
    (fixedLocalCoefficient basis coefficient space)

/-- The coordinatewise open interior of one fixed spatial box. -/
def DiracMatterSpatialBoxInterior
    (a b space : DiracMatterSpatialCoordinates) : Prop :=
  ∀ direction, a direction < space direction ∧ space direction < b direction

/-- Every basis function vanishes outside the coordinatewise open interior of
the same spatial box. -/
def DiracMatterSpatialBasisSupportedInBoxInterior
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (a b : DiracMatterSpatialCoordinates) : Prop :=
  ∀ mode space, ¬ DiracMatterSpatialBoxInterior a b space →
    basis mode space = 0

private theorem spatialSynthesis_eq_zero_of_not_mem_boxInterior
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : ¬ DiracMatterSpatialBoxInterior a b space) :
    diracMatterSpatialGalerkinSynthesis basis coefficient space = 0 := by
  apply matterCoordinateEquiv.injective
  simp [diracMatterSpatialGalerkinSynthesis_coordinates,
    basisZeroOutside _ space spaceOutside]

private theorem fixedWeakMassDensity_bilinear_eq_zero_of_not_mem_box
    {candidateModeCount : ℕ}
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient candidateModeCount)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    diracMatterWeakMassDensity matrix basis first second space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    constructor
    · intro direction
      exact (spaceInterior direction).1.le
    · intro direction
      exact (spaceInterior direction).2.le
  have firstZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    first a b basisZeroOutside space outsideInterior
  unfold diracMatterWeakMassDensity
  rw [firstZero]
  simp [diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing, dotProduct]

private theorem fixedWeakStiffnessDensity_bilinear_eq_zero_of_not_mem_box
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    diracMatterWeakStiffnessDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
        (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
        first second space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    constructor
    · intro direction
      exact (spaceInterior direction).1.le
    · intro direction
      exact (spaceInterior direction).2.le
  have firstZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    first a b basisZeroOutside space outsideInterior
  unfold diracMatterWeakStiffnessDensity
  rw [firstZero]
  simp [diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing, dotProduct]

private theorem fixedSpatialEnergyFlux_zeroOnBoxBoundary
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    DiracMatterSpatialFluxZeroOnBoxBoundary
      (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
        time)
      a b := by
  intro direction point _
  have frontOutside : ¬ DiracMatterSpatialBoxInterior a b
      (direction.insertNth (b direction) point) := by
    intro frontInterior
    have strict := (frontInterior direction).2
    simpa using strict
  have backOutside : ¬ DiracMatterSpatialBoxInterior a b
      (direction.insertNth (a direction) point) := by
    intro backInterior
    have strict := (backInterior direction).1
    simpa using strict
  have frontFieldZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    coefficient a b basisZeroOutside
    (direction.insertNth (b direction) point) frontOutside
  have backFieldZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    coefficient a b basisZeroOutside
    (direction.insertNth (a direction) point) backOutside
  constructor
  · simp only [diracMatterSpatialEnergyFlux]
    rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice, frontFieldZero]
    simp [diracMatterEnergyFlux, diracExteriorMatterCoordinateEnergy,
      diracExteriorMatterCoordinatePairing, dotProduct]
  · simp only [diracMatterSpatialEnergyFlux]
    rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice, backFieldZero]
    simp [diracMatterEnergyFlux, diracExteriorMatterCoordinateEnergy,
      diracExteriorMatterCoordinatePairing, dotProduct]

private theorem fixedSpatialBilinearFlux_zeroOnBoxBoundary
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    DiracMatterSpatialFluxZeroOnBoxBoundary
      (diracMatterSpatialBilinearFlux fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first)
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second)
        time)
      a b := by
  intro direction point _
  have frontOutside : ¬ DiracMatterSpatialBoxInterior a b
      (direction.insertNth (b direction) point) := by
    intro frontInterior
    have strict := (frontInterior direction).2
    simpa using strict
  have backOutside : ¬ DiracMatterSpatialBoxInterior a b
      (direction.insertNth (a direction) point) := by
    intro backInterior
    have strict := (backInterior direction).1
    simpa using strict
  have frontFieldZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    first a b basisZeroOutside
    (direction.insertNth (b direction) point) frontOutside
  have backFieldZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    first a b basisZeroOutside
    (direction.insertNth (a direction) point) backOutside
  constructor
  · simp only [diracMatterSpatialBilinearFlux]
    rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice,
      fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice, frontFieldZero]
    simp [diracMatterBilinearFlux,
      diracExteriorMatterCoordinatePairing, dotProduct]
  · simp only [diracMatterSpatialBilinearFlux]
    rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice,
      fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice, backFieldZero]
    simp [diracMatterBilinearFlux,
      diracExteriorMatterCoordinatePairing, dotProduct]

/-- Green transport for the fixed action coefficients.  The derivative on the
trial and the derivative on the fixed test occur in one exact box identity;
no mode-dependent inverse or residual is used. -/
private theorem integral_fixedSpatialBilinearGreenCombination_eq_zero
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (first second : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    (∫ space in Icc a b,
        spatialBilinearPrincipalPairing basis second first time space +
          spatialBilinearPrincipalPairing basis first second time space +
          ∑ direction : Fin 3,
            diracMatterWeakMassDensity
              (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
                direction.succ time)
              basis first second space) = 0 := by
  let flux := diracMatterSpatialBilinearFlux fixedEvolutionPrincipal
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first)
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second)
    time
  have fluxRegular : ∀ direction : Fin 3, ContDiff ℝ 1 (flux direction) :=
    fun direction ↦
      fixedSpatialBilinearFlux_contDiff_one basis basisRegular first second time
        direction
  have boundaryZero : DiracMatterSpatialFluxZeroOnBoxBoundary flux a b :=
    fixedSpatialBilinearFlux_zeroOnBoxBoundary basis first second time a b
      basisZeroOutside
  calc
    (∫ space in Icc a b,
        spatialBilinearPrincipalPairing basis second first time space +
          spatialBilinearPrincipalPairing basis first second time space +
          ∑ direction : Fin 3,
            diracMatterWeakMassDensity
              (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
                direction.succ time)
              basis first second space) =
        ∫ space in Icc a b,
          diracMatterSpatialFluxDivergence flux space := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro space _
      exact (fixedSpatialBilinearFluxDivergence_eq basis basisRegular
        first second time space).symm
    _ = 0 := integral_diracMatterSpatialFluxDivergence_box_eq_zero
      flux a b boxOrder fluxRegular boundaryZero

private theorem fixedWeakEnergyDensity_eq_zero_of_not_mem_box
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    fixedWeakEnergyDensity basis coefficient time space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    constructor
    · intro direction
      exact (spaceInterior direction).1.le
    · intro direction
      exact (spaceInterior direction).2.le
  have fieldZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    coefficient a b basisZeroOutside space outsideInterior
  unfold fixedWeakEnergyDensity diracMatterWeakMassDensity
  rw [fieldZero]
  simp [diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing]

private theorem fixedWeakTemporalEnergyDensity_eq_zero_of_not_mem_box
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    fixedWeakTemporalEnergyDensity basis coefficient time space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    constructor
    · intro direction
      exact (spaceInterior direction).1.le
    · intro direction
      exact (spaceInterior direction).2.le
  have fieldZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    coefficient a b basisZeroOutside space outsideInterior
  have densityCurveZero :
      (fun candidateTime ↦
        diracMatterWeakMassDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
          basis coefficient coefficient space) =
        fun _candidateTime ↦ (0 : ℝ) := by
    funext candidateTime
    unfold diracMatterWeakMassDensity
    rw [fieldZero]
    simp [diracExteriorMatterEnergyPairing,
      diracExteriorMatterCoordinatePairing]
  let density : ℝ → DiracMatterSpatialCoordinates → ℝ :=
    fun candidateTime candidateSpace ↦
      diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
        basis coefficient coefficient candidateSpace
  have densityC1 : ContDiff ℝ 1 (Function.uncurry density) :=
    diracMatterWeakMassDensity_joint_contDiff_one
      fixedP506L0CauchySafeMatterWeakMassMatrix basis
      (fun row column ↦
        (fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff row column
          ).of_le (by norm_num))
      basisRegular coefficient coefficient
  have temporalDerivative :=
    diracMatterSpatialEnergyTimeDerivative_hasDerivAt density densityC1 time
      space
  have temporalZero :
      diracMatterSpatialEnergyTimeDerivative density time space = 0 := by
    rw [show (density · space) = fun _candidateTime ↦ (0 : ℝ) by
      exact densityCurveZero] at temporalDerivative
    exact temporalDerivative.unique (hasDerivAt_const time 0)
  exact temporalZero

private theorem fixedWeakStiffnessEnergyDensity_eq_zero_of_not_mem_box
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    fixedWeakStiffnessEnergyDensity basis coefficient time space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    constructor
    · intro direction
      exact (spaceInterior direction).1.le
    · intro direction
      exact (spaceInterior direction).2.le
  have fieldZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
    coefficient a b basisZeroOutside space outsideInterior
  unfold fixedWeakStiffnessEnergyDensity diracMatterWeakStiffnessDensity
  rw [fieldZero]
  simp [diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing, dotProduct]

private theorem fixedWeakEnergyRateDensity_eq_zero_of_not_mem_box
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    fixedWeakEnergyRateDensity basis coefficient time space = 0 := by
  rw [fixedWeakEnergyRateDensity,
    fixedWeakTemporalEnergyDensity_eq_zero_of_not_mem_box basis basisRegular
      coefficient time a b basisZeroOutside space spaceOutside,
    fixedWeakStiffnessEnergyDensity_eq_zero_of_not_mem_box basis coefficient
      time a b basisZeroOutside space spaceOutside]
  ring

private theorem fixedWeakTemporalEnergyDensity_continuous
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) :
    Continuous (fixedWeakTemporalEnergyDensity basis coefficient time) := by
  let density : ℝ → DiracMatterSpatialCoordinates → ℝ :=
    fun candidateTime candidateSpace ↦
      diracMatterWeakMassDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix candidateTime)
        basis coefficient coefficient candidateSpace
  have densityC1 : ContDiff ℝ 1 (Function.uncurry density) :=
    diracMatterWeakMassDensity_joint_contDiff_one
      fixedP506L0CauchySafeMatterWeakMassMatrix basis
      (fun row column ↦
        (fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff row column
          ).of_le (by norm_num))
      basisRegular coefficient coefficient
  have actual :=
    diracMatterSpatialEnergyTimeDerivative_continuous density densityC1 time
  convert actual using 1
  funext space
  rfl

private theorem fixedWeakStiffnessEnergyDensity_continuous
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ) :
    Continuous (fixedWeakStiffnessEnergyDensity basis coefficient time) := by
  exact fixedWeakStiffnessDensity_continuous basis basisRegular coefficient time

private theorem fixedGalerkinWeakTestPairingRate_eq_box_green
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (trial : ℝ → DiracMatterGalerkinCoefficient candidateModeCount)
    (test : DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    galerkinWeakTestPairingRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
          basisCompact)
        (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact)
        trial test time =
      ∫ space in Icc a b,
        fixedWeakTestGreenRateDensity basis (trial time) test time space := by
  let coefficient := trial time
  let massDensity : DiracMatterSpatialCoordinates → ℝ :=
    fun space ↦
      diracMatterWeakMassDensity
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection time)
        basis coefficient test space
  let stiffnessDensity : DiracMatterSpatialCoordinates → ℝ :=
    fun space ↦
      diracMatterWeakStiffnessDensity
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
        (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
        test coefficient space
  let greenCombination : DiracMatterSpatialCoordinates → ℝ :=
    fun space ↦
      spatialBilinearPrincipalPairing basis coefficient test time space +
        spatialBilinearPrincipalPairing basis test coefficient time space +
        ∑ direction : Fin 3,
          diracMatterWeakMassDensity
            (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
              direction.succ time)
            basis test coefficient space
  have massContinuous : Continuous massDensity :=
    diracMatterWeakMassDensity_continuous
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection time)
      basis
      (fun row column ↦
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
          canonicalLorentzianTimeDirection row column).comp
          (continuous_const.prodMk continuous_id))
      (fun mode ↦ (basisRegular mode).continuous)
      coefficient test
  have stiffnessContinuous : Continuous stiffnessDensity := by
    exact fixedWeakStiffnessDensity_bilinear_continuous basis basisRegular
      test coefficient time
  have massIntegrable : IntegrableOn massDensity (Icc a b) :=
    massContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have stiffnessIntegrable : IntegrableOn stiffnessDensity (Icc a b) :=
    stiffnessContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have originalIntegrable : IntegrableOn
      (fun space ↦ massDensity space - stiffnessDensity space) (Icc a b) :=
    massIntegrable.sub stiffnessIntegrable
  let flux := diracMatterSpatialBilinearFlux fixedEvolutionPrincipal
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test)
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
    time
  have fluxRegular : ∀ direction : Fin 3, ContDiff ℝ 1 (flux direction) :=
    fun direction ↦
      fixedSpatialBilinearFlux_contDiff_one basis basisRegular test coefficient
        time direction
  have greenEq : greenCombination =
      diracMatterSpatialFluxDivergence flux := by
    funext space
    exact (fixedSpatialBilinearFluxDivergence_eq basis basisRegular
      test coefficient time space).symm
  have greenIntegrable : IntegrableOn greenCombination (Icc a b) := by
    rw [greenEq]
    exact (diracMatterSpatialFluxDivergence_continuous flux fluxRegular
      ).continuousOn.integrableOn_compact isCompact_Icc
  have greenIntegralZero :
      (∫ space in Icc a b, greenCombination space) = 0 := by
    exact integral_fixedSpatialBilinearGreenCombination_eq_zero basis
      basisRegular test coefficient time a b boxOrder basisZeroOutside
  have massDerivativeEq :
      fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
          basisCompact time coefficient test =
        ∫ space, massDensity space := by
    rw [fixedP506L0CauchySafeMatterWeakMassFormDerivative_apply]
    unfold diracMatterWeakMassFormValueTimeDerivative
    apply integral_congr_ae
    filter_upwards with space
    exact fixedWeakMassDensity_timeDerivative_bilinear_eq basis basisRegular
      coefficient test time space
  have stiffnessFormEq :
      fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact time coefficient test =
        ∫ space, stiffnessDensity space := by
    unfold fixedP506L0CauchySafeMatterWeakStiffnessForm
    rw [diracMatterWeakStiffnessForm_apply]
    rfl
  have massSetIntegralEq :
      (∫ space in Icc a b, massDensity space) = ∫ space, massDensity space :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun space spaceOutside ↦
        fixedWeakMassDensity_bilinear_eq_zero_of_not_mem_box
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection time)
          basis coefficient test a b basisZeroOutside space spaceOutside)
  have stiffnessSetIntegralEq :
      (∫ space in Icc a b, stiffnessDensity space) =
        ∫ space, stiffnessDensity space :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun space spaceOutside ↦
        fixedWeakStiffnessDensity_bilinear_eq_zero_of_not_mem_box basis
          test coefficient time a b basisZeroOutside space spaceOutside)
  have originalEq :
      galerkinWeakTestPairingRate
          (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
            basisCompact)
          (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
            basisCompact)
          trial test time =
        ∫ space in Icc a b,
          (massDensity space - stiffnessDensity space) := by
    unfold galerkinWeakTestPairingRate
    rw [massDerivativeEq, stiffnessFormEq, ← massSetIntegralEq,
      ← stiffnessSetIntegralEq]
    exact (integral_sub massIntegrable stiffnessIntegrable).symm
  calc
    galerkinWeakTestPairingRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
          basisCompact)
        (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact)
        trial test time =
      ∫ space in Icc a b,
        (massDensity space - stiffnessDensity space) := originalEq
    _ = (∫ space in Icc a b,
          (massDensity space - stiffnessDensity space)) +
        ∫ space in Icc a b, greenCombination space := by
      rw [greenIntegralZero, add_zero]
    _ = ∫ space in Icc a b,
        ((massDensity space - stiffnessDensity space) +
          greenCombination space) :=
      (integral_add originalIntegrable greenIntegrable).symm
    _ = ∫ space in Icc a b,
        fixedWeakTestGreenRateDensity basis coefficient test time space := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro space _
      simp only [massDensity, stiffnessDensity, greenCombination]
      rw [fixedWeakStiffnessDensity_eq_constant_add_bilinearPrincipal basis
        basisRegular test coefficient time space]
      unfold fixedWeakTestGreenRateDensity
      ring

/-- A fixed physical test field generates one weak-pairing value bound shared
by every later finite Galerkin carrier.  The bound is selected on the physical
time-space box before the mode count. -/
theorem exists_fixedModeUniformGalerkinWeakTestPairingBoundOnBox
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (coefficient : ℝ → DiracMatterGalerkinCoefficient candidateModeCount)
        (test : DiracMatterGalerkinCoefficient candidateModeCount),
        (testCoordinates = fun point ↦
          matterCoordinateEquiv
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point)) →
        ∀ time ∈ Icc timeStart timeEnd,
          ‖galerkinWeakTestPairing
              (fixedP506L0CauchySafeMatterWeakMassForm basis
                (fun mode ↦ (basisRegular mode).continuous) basisCompact)
              coefficient test time‖ ≤
            C * ((∫ space in Icc a b,
                ‖matterCoordinateEquiv
                  (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
                    space)‖ ^ 2) + volume.real (Icc a b)) := by
  obtain ⟨C, CNonnegative, pointwiseBound⟩ :=
    exists_fixedWeakTestPointwiseMassPairingBoundOnBox testCoordinates
      testRegular timeStart timeEnd a b timeOrder boxOrder
  refine ⟨C, CNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient test testRepresentation time timeMem
  let density : DiracMatterSpatialCoordinates → ℝ := fun space ↦
    diracMatterWeakMassDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      basis (coefficient time) test space
  let coordinatePath : DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
    fun space ↦ matterCoordinateEquiv
      (diracMatterSpatialGalerkinSynthesis basis (coefficient time) space)
  have coordinatePathContinuous : Continuous coordinatePath :=
    diracMatterSpatialGalerkinSynthesis_coordinates_continuous basis
      (fun mode ↦ (basisRegular mode).continuous) (coefficient time)
  have densityContinuous : Continuous density := by
    exact diracMatterWeakMassDensity_continuous
      (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
      (diracMatterWeakMassMatrix_spatial_continuous
        fixedP506L0CauchySafeMatterWeakMassMatrix
        fixedP506L0CauchySafeMatterWeakMassMatrix_continuous time)
      (fun mode ↦ (basisRegular mode).continuous) (coefficient time) test
  have densityIntegrable : IntegrableOn density (Icc a b) :=
    densityContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have normSquareIntegrable : IntegrableOn (fun space ↦
      ‖coordinatePath space‖ ^ 2) (Icc a b) :=
    coordinatePathContinuous.norm.pow 2 |>.continuousOn.integrableOn_compact
      isCompact_Icc
  have oneIntegrable : IntegrableOn
      (fun _space : DiracMatterSpatialCoordinates ↦ (1 : ℝ)) (Icc a b) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have upperIntegrable : IntegrableOn (fun space ↦
      C * (‖coordinatePath space‖ ^ 2 + 1)) (Icc a b) :=
    (normSquareIntegrable.add oneIntegrable).const_mul C
  have pointwiseBoundAE : ∀ᵐ space ∂volume.restrict (Icc a b),
      ‖density space‖ ≤ C * (‖coordinatePath space‖ ^ 2 + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
    exact fixedWeakMassDensity_norm_le_of_pointwiseMassPairingBound C
      CNonnegative basis (coefficient time) test testCoordinates
      testRepresentation time space
      (pointwiseBound (time, space) ⟨timeMem, spaceMem⟩
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis (coefficient time) space)))
  have densitySetIntegral :
      (∫ space in Icc a b, density space) = ∫ space, density space :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun space spaceOutside ↦
        fixedWeakMassDensity_bilinear_eq_zero_of_not_mem_box
          (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
          (coefficient time) test a b basisZeroOutside space spaceOutside)
  have pairingEq :
      galerkinWeakTestPairing
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient test time = ∫ space in Icc a b, density space := by
    unfold galerkinWeakTestPairing
      fixedP506L0CauchySafeMatterWeakMassForm
    rw [diracMatterWeakMassForm_apply]
    exact densitySetIntegral.symm
  calc
    ‖galerkinWeakTestPairing
        (fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact)
        coefficient test time‖ = ‖∫ space in Icc a b, density space‖ := by
      rw [pairingEq]
    _ ≤ ∫ space in Icc a b, ‖density space‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ space in Icc a b,
        C * (‖coordinatePath space‖ ^ 2 + 1) :=
      integral_mono_ae densityIntegrable.norm upperIntegrable pointwiseBoundAE
    _ = C * (∫ space in Icc a b,
        (‖coordinatePath space‖ ^ 2 + 1)) := by
      rw [integral_const_mul]
    _ = C * ((∫ space in Icc a b, ‖coordinatePath space‖ ^ 2) +
        ∫ _space in Icc a b, (1 : ℝ)) := by
      rw [integral_add normSquareIntegrable oneIntegrable]
    _ = C * ((∫ space in Icc a b,
        ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
            space)‖ ^ 2) + volume.real (Icc a b)) := by
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, mul_one]
      rfl

/-- A fixed physical test field generates one weak-pairing rate bound shared
by every later finite Galerkin carrier.  Green transport removes all spatial
derivatives of the varying trial before this constant is selected. -/
theorem exists_fixedModeUniformGalerkinWeakTestPairingRateBoundOnBox
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (trial : ℝ → DiracMatterGalerkinCoefficient candidateModeCount)
        (test : DiracMatterGalerkinCoefficient candidateModeCount),
        (testCoordinates = fun point ↦
          matterCoordinateEquiv
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point)) →
        ∀ time ∈ Icc timeStart timeEnd,
          ‖galerkinWeakTestPairingRate
              (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis
                basisRegular basisCompact)
              (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
                basisCompact)
              trial test time‖ ≤
            C * ((∫ space in Icc a b,
                ‖matterCoordinateEquiv
                  (diracMatterSpatialGalerkinSynthesis basis (trial time)
                    space)‖ ^ 2) + volume.real (Icc a b)) := by
  obtain ⟨C, CNonnegative, pointwiseBound⟩ :=
    exists_fixedWeakTestPointwiseGreenRateBoundOnBox testCoordinates
      testRegular timeStart timeEnd a b timeOrder boxOrder
  refine ⟨C, CNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    trial test testRepresentation time timeMem
  let density : DiracMatterSpatialCoordinates → ℝ :=
    fixedWeakTestGreenRateDensity basis (trial time) test time
  let coordinatePath : DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
    fun space ↦ matterCoordinateEquiv
      (diracMatterSpatialGalerkinSynthesis basis (trial time) space)
  let localTrial : DiracMatterSpatialCoordinates →
      DiracMatterGalerkinCoefficient 1 :=
    fun space ↦ fiberCoefficientCLM (coordinatePath space)
  have coordinatePathContinuous : Continuous coordinatePath :=
    diracMatterSpatialGalerkinSynthesis_coordinates_continuous basis
      (fun mode ↦ (basisRegular mode).continuous) (trial time)
  have localTrialContinuous : Continuous localTrial :=
    fiberCoefficientCLM.continuous.comp coordinatePathContinuous
  have densityContinuous : Continuous density := by
    let inputPath : DiracMatterSpatialCoordinates →
        (ℝ × DiracMatterSpatialCoordinates) ×
          DiracMatterGalerkinCoefficient 1 :=
      fun space ↦ ((time, space), localTrial space)
    have inputPathContinuous : Continuous inputPath :=
      (continuous_const.prodMk continuous_id).prodMk localTrialContinuous
    have transported :=
      (fixedWeakTestPointwiseGreenRate_joint_continuous testCoordinates
        testRegular).comp inputPathContinuous
    convert transported using 1
    funext space
    exact fixedWeakTestGreenRateDensity_eq_pointwise basis (trial time) test
      testCoordinates testRepresentation time space
  have densityIntegrable : IntegrableOn density (Icc a b) :=
    densityContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have normSquareContinuous : Continuous (fun space ↦
      ‖coordinatePath space‖ ^ 2) := coordinatePathContinuous.norm.pow 2
  have normSquareIntegrable : IntegrableOn (fun space ↦
      ‖coordinatePath space‖ ^ 2) (Icc a b) :=
    normSquareContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have oneIntegrable : IntegrableOn
      (fun _space : DiracMatterSpatialCoordinates ↦ (1 : ℝ)) (Icc a b) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have upperIntegrable : IntegrableOn (fun space ↦
      C * (‖coordinatePath space‖ ^ 2 + 1)) (Icc a b) :=
    (normSquareIntegrable.add oneIntegrable).const_mul C
  have pointwiseBoundAE : ∀ᵐ space ∂volume.restrict (Icc a b),
      ‖density space‖ ≤ C * (‖coordinatePath space‖ ^ 2 + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
    exact fixedWeakTestGreenRateDensity_norm_le C CNonnegative basis
      (trial time) test testCoordinates testRepresentation time space
      (pointwiseBound (time, space) ⟨timeMem, spaceMem⟩
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis (trial time) space)))
  have rateEq := fixedGalerkinWeakTestPairingRate_eq_box_green basis
    basisRegular basisCompact trial test time a b boxOrder basisZeroOutside
  calc
    ‖galerkinWeakTestPairingRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
          basisCompact)
        (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact)
        trial test time‖ = ‖∫ space in Icc a b, density space‖ := by
      rw [rateEq]
    _ ≤ ∫ space in Icc a b, ‖density space‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ space in Icc a b,
        C * (‖coordinatePath space‖ ^ 2 + 1) :=
      integral_mono_ae densityIntegrable.norm upperIntegrable pointwiseBoundAE
    _ = C * (∫ space in Icc a b,
        (‖coordinatePath space‖ ^ 2 + 1)) := by
      rw [integral_const_mul]
    _ = C * ((∫ space in Icc a b, ‖coordinatePath space‖ ^ 2) +
        ∫ _space in Icc a b, (1 : ℝ)) := by
      rw [integral_add normSquareIntegrable oneIntegrable]
    _ = C * ((∫ space in Icc a b,
        ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis (trial time) space)‖ ^ 2) +
        volume.real (Icc a b)) := by
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, mul_one]
      rfl

private theorem fixedGalerkinWeakEnergy_eq_box
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : ℝ → DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    galerkinWeakEnergy
        (fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact)
        coefficient time =
      ∫ space in Icc a b,
        fixedWeakEnergyDensity basis (coefficient time) time space := by
  have setIntegralEq :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun space spaceOutside ↦
        fixedWeakEnergyDensity_eq_zero_of_not_mem_box basis (coefficient time)
          time a b basisZeroOutside space spaceOutside)
  unfold galerkinWeakEnergy fixedP506L0CauchySafeMatterWeakMassForm
  change diracMatterWeakMassFormValue
      (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
      (coefficient time) (coefficient time) = _
  unfold diracMatterWeakMassFormValue
  exact setIntegralEq.symm

/-- One strict action-owned coercivity constant controls the spatial
`L²` density of every later finite Galerkin synthesis in the fixed box. -/
theorem exists_fixedModeUniformGalerkinWeakEnergyCoercivityOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (coefficient : ℝ →
          DiracMatterGalerkinCoefficient candidateModeCount)
        (time : ℝ),
        time ∈ Icc timeStart timeEnd →
        κ * ∫ space in Icc a b,
            ‖matterCoordinateEquiv
              (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
                space)‖ ^ 2 ≤
          galerkinWeakEnergy
            (fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact)
            coefficient time := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have carrierNonempty : carrier.Nonempty := by
    refine ⟨(timeStart, a), ?_⟩
    exact ⟨⟨le_rfl, timeOrder⟩, ⟨le_rfl, boxOrder⟩⟩
  obtain ⟨κ, κPositive, pointwiseCoercivity⟩ :=
    exists_fixedModeUniformPointwiseEnergyCoercivity carrier carrierCompact
      carrierNonempty
  refine ⟨κ, κPositive, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient time timeMem
  have pointwiseBound : ∀ space ∈ Icc a b,
      κ * ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
            space)‖ ^ 2 ≤
        fixedWeakPointwiseEnergyDensity basis (coefficient time) time space := by
    intro space spaceMem
    have localNorm :
        ‖fixedLocalCoefficient basis (coefficient time) space‖ =
          ‖matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
              space)‖ := by
      exact fiberCoefficient_norm _
    calc
      κ * ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
            space)‖ ^ 2 =
          κ * ‖fixedLocalCoefficient basis (coefficient time) space‖ ^ 2 := by
        rw [localNorm]
      _ ≤ fixedWeakPointwiseEnergyDensity basis (coefficient time) time
          space := by
        simpa [fixedWeakPointwiseEnergyDensity] using
          pointwiseCoercivity (time, space) ⟨timeMem, spaceMem⟩
            (fixedLocalCoefficient basis (coefficient time) space)
  have boxCoercivity := fixedWeakEnergyCoercivityOnBox_of_pointwiseBound κ
    basis (fun mode ↦ (basisRegular mode).continuous) (coefficient time) time
    a b pointwiseBound
  rw [fixedGalerkinWeakEnergy_eq_box basis basisRegular basisCompact
    coefficient time a b basisZeroOutside]
  exact boxCoercivity

private theorem fixedGalerkinWeakEnergyRate_eq_box
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : ℝ → DiracMatterGalerkinCoefficient candidateModeCount)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    galerkinWeakEnergyRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
          basisCompact)
        (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact)
        coefficient time =
      ∫ space in Icc a b,
        fixedWeakEnergyRateDensity basis (coefficient time) time space := by
  have temporalSetIntegralEq :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun space spaceOutside ↦
        fixedWeakTemporalEnergyDensity_eq_zero_of_not_mem_box basis basisRegular
          (coefficient time) time a b basisZeroOutside space spaceOutside)
  have stiffnessSetIntegralEq :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (fun space spaceOutside ↦
        fixedWeakStiffnessEnergyDensity_eq_zero_of_not_mem_box basis
          (coefficient time) time a b basisZeroOutside space spaceOutside)
  have temporalIntegrable : IntegrableOn
      (fixedWeakTemporalEnergyDensity basis (coefficient time) time)
      (Icc a b) :=
    (fixedWeakTemporalEnergyDensity_continuous basis basisRegular
      (coefficient time) time).continuousOn.integrableOn_compact isCompact_Icc
  have stiffnessIntegrable : IntegrableOn
      (fixedWeakStiffnessEnergyDensity basis (coefficient time) time)
      (Icc a b) :=
    (fixedWeakStiffnessEnergyDensity_continuous basis basisRegular
      (coefficient time) time).continuousOn.integrableOn_compact isCompact_Icc
  unfold galerkinWeakEnergyRate
  rw [fixedP506L0CauchySafeMatterWeakMassFormDerivative_apply]
  change (∫ space,
      fixedWeakTemporalEnergyDensity basis (coefficient time) time space) -
      2 * (∫ space,
        fixedWeakStiffnessEnergyDensity basis (coefficient time) time space) = _
  rw [← temporalSetIntegralEq, ← stiffnessSetIntegralEq]
  rw [← integral_const_mul]
  rw [← integral_sub temporalIntegrable (stiffnessIntegrable.const_mul 2)]
  rfl

/-- One action-owned rate constant controls the complete weak energy rate for
every later finite mode carrier supported in the fixed box. -/
theorem exists_fixedModeUniformGalerkinWeakEnergyRateBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (coefficient : ℝ →
          DiracMatterGalerkinCoefficient candidateModeCount)
        (time : ℝ),
        time ∈ Icc timeStart timeEnd →
        ‖galerkinWeakEnergyRate
            (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis
              basisRegular basisCompact)
            (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
              basisCompact)
            coefficient time‖ ≤
          K * galerkinWeakEnergy
            (fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact)
            coefficient time := by
  obtain ⟨K, KNonnegative, boxBound⟩ :=
    exists_fixedModeUniformWeakEnergyRateBoundOnBox timeStart timeEnd a b
      timeOrder boxOrder
  refine ⟨K, KNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient time timeMem
  have boundaryZero := fixedSpatialEnergyFlux_zeroOnBoxBoundary basis
    (coefficient time) time a b basisZeroOutside
  have estimate := boxBound candidateModeCount basis basisRegular
    (coefficient time) time timeMem boundaryZero
  rw [fixedGalerkinWeakEnergyRate_eq_box basis basisRegular basisCompact
    coefficient time a b basisZeroOutside]
  rw [fixedGalerkinWeakEnergy_eq_box basis basisRegular basisCompact
    coefficient time a b basisZeroOutside]
  exact estimate

private theorem fixedGalerkinWeakEnergy_norm_le
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient velocity : ℝ →
      DiracMatterGalerkinCoefficient candidateModeCount)
    (timeStart timeEnd K : ℝ)
    (evolution : ∀ time ∈ Icc timeStart timeEnd,
      HasDerivWithinAt coefficient (velocity time)
        (Icc timeStart timeEnd) time)
    (weakEquation : ∀ time ∈ Icc timeStart timeEnd,
      fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact time
          (velocity time) (coefficient time) +
        fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact time (coefficient time) (coefficient time) = 0)
    (rateBound : ∀ time ∈ Ico timeStart timeEnd,
      ‖galerkinWeakEnergyRate
          (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
            basisCompact)
          (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
            basisCompact)
          coefficient time‖ ≤
        K * galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient time) :
    ∀ time ∈ Icc timeStart timeEnd,
      ‖galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient time‖ ≤
        ‖galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient timeStart‖ *
          Real.exp (K * (time - timeStart)) := by
  apply galerkinWeakEnergy_norm_le_of_modeUniformRate
    (fixedP506L0CauchySafeMatterWeakMassForm basis
      (fun mode ↦ (basisRegular mode).continuous) basisCompact)
    (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
      basisCompact)
    (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
      basisCompact)
    coefficient velocity timeStart timeEnd K
  · intro time _
    exact (fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt basis
      basisRegular basisCompact time).hasDerivWithinAt
  · intro time timeMem
    exact
      (evolution time (Ico_subset_Icc_self timeMem)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem timeMem)
  · intro time _ first second
    exact fixedP506L0CauchySafeMatterWeakMassForm_symm basis
      (fun mode ↦ (basisRegular mode).continuous) basisCompact time first second
  · intro time timeMem
    exact weakEquation time (Ico_subset_Icc_self timeMem)
  · intro time timeMem
    exact (galerkinWeakEnergy_hasDerivWithinAt
      (fixedP506L0CauchySafeMatterWeakMassForm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
      (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
        basisCompact)
      (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
        basisCompact)
      coefficient (velocity time) (Icc timeStart timeEnd) time
      (fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt basis basisRegular
        basisCompact time).hasDerivWithinAt
      (evolution time timeMem)
      (fixedP506L0CauchySafeMatterWeakMassForm_symm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact time)
      (weakEquation time timeMem)).continuousWithinAt
  · intro time timeMem
    have energyNonnegative : 0 ≤ galerkinWeakEnergy
        (fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact)
        coefficient time :=
      fixedP506L0CauchySafeMatterWeakMassForm_nonnegative basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact time
        (coefficient time)
    rw [Real.norm_of_nonneg energyNonnegative]
    exact rateBound time timeMem

/-- The generated rate constant gives a Grönwall estimate uniformly in the
finite mode count for every coefficient curve satisfying the weak equation. -/
theorem exists_fixedModeUniformGalerkinWeakEnergyGronwallOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (coefficient velocity : ℝ →
          DiracMatterGalerkinCoefficient candidateModeCount),
        (∀ time ∈ Icc timeStart timeEnd,
          HasDerivWithinAt coefficient (velocity time)
            (Icc timeStart timeEnd) time) →
        (∀ time ∈ Icc timeStart timeEnd,
          fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact time
              (velocity time) (coefficient time) +
            fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
              basisCompact time (coefficient time) (coefficient time) = 0) →
        ∀ time ∈ Icc timeStart timeEnd,
          ‖galerkinWeakEnergy
              (fixedP506L0CauchySafeMatterWeakMassForm basis
                (fun mode ↦ (basisRegular mode).continuous) basisCompact)
              coefficient time‖ ≤
            ‖galerkinWeakEnergy
              (fixedP506L0CauchySafeMatterWeakMassForm basis
                (fun mode ↦ (basisRegular mode).continuous) basisCompact)
              coefficient timeStart‖ *
              Real.exp (K * (time - timeStart)) := by
  obtain ⟨K, KNonnegative, rateBound⟩ :=
    exists_fixedModeUniformGalerkinWeakEnergyRateBoundOnBox
      timeStart timeEnd a b timeOrder boxOrder
  refine ⟨K, KNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient velocity evolution weakEquation
  exact fixedGalerkinWeakEnergy_norm_le basis basisRegular basisCompact
    coefficient velocity timeStart timeEnd K evolution weakEquation
    (fun time timeMem ↦
      rateBound candidateModeCount basis basisRegular basisCompact
        basisZeroOutside coefficient time (Ico_subset_Icc_self timeMem))

/-- The same two action-owned constants turn the finite weak equation into a
mode-uniform spatial `L²` bound on the common spacetime box. -/
theorem exists_fixedModeUniformGalerkinSpatialL2BoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ κ K : ℝ, 0 < κ ∧ 0 ≤ K ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (coefficient velocity : ℝ →
          DiracMatterGalerkinCoefficient candidateModeCount),
        (∀ time ∈ Icc timeStart timeEnd,
          HasDerivWithinAt coefficient (velocity time)
            (Icc timeStart timeEnd) time) →
        (∀ time ∈ Icc timeStart timeEnd,
          fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact time
              (velocity time) (coefficient time) +
            fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
              basisCompact time (coefficient time) (coefficient time) = 0) →
        ∀ time ∈ Icc timeStart timeEnd,
          (∫ space in Icc a b,
              ‖matterCoordinateEquiv
                (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
                  space)‖ ^ 2) ≤
            κ⁻¹ *
              (‖galerkinWeakEnergy
                  (fixedP506L0CauchySafeMatterWeakMassForm basis
                    (fun mode ↦ (basisRegular mode).continuous) basisCompact)
                  coefficient timeStart‖ *
                Real.exp (K * (time - timeStart))) := by
  obtain ⟨κ, κPositive, coercivity⟩ :=
    exists_fixedModeUniformGalerkinWeakEnergyCoercivityOnBox
      timeStart timeEnd a b timeOrder boxOrder
  obtain ⟨K, KNonnegative, energyGrowth⟩ :=
    exists_fixedModeUniformGalerkinWeakEnergyGronwallOnBox
      timeStart timeEnd a b timeOrder boxOrder
  refine ⟨κ, K, κPositive, KNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient velocity evolution weakEquation time timeMem
  have energyCoercivity := coercivity candidateModeCount basis basisRegular
    basisCompact basisZeroOutside coefficient time timeMem
  have growthBound := energyGrowth candidateModeCount basis basisRegular
    basisCompact basisZeroOutside coefficient velocity evolution weakEquation
    time timeMem
  have energyNonnegative : 0 ≤ galerkinWeakEnergy
      (fixedP506L0CauchySafeMatterWeakMassForm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
      coefficient time :=
    fixedP506L0CauchySafeMatterWeakMassForm_nonnegative basis
      (fun mode ↦ (basisRegular mode).continuous) basisCompact time
      (coefficient time)
  have scaledL2Bound :
      κ * ∫ space in Icc a b,
          ‖matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
              space)‖ ^ 2 ≤
        ‖galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient timeStart‖ *
          Real.exp (K * (time - timeStart)) := by
    calc
      κ * ∫ space in Icc a b,
          ‖matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
              space)‖ ^ 2 ≤
          galerkinWeakEnergy
            (fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact)
            coefficient time := energyCoercivity
      _ = ‖galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient time‖ := (Real.norm_of_nonneg energyNonnegative).symm
      _ ≤ ‖galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient timeStart‖ *
          Real.exp (K * (time - timeStart)) := growthBound
  calc
    (∫ space in Icc a b,
        ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
            space)‖ ^ 2) =
        κ⁻¹ *
          (κ * ∫ space in Icc a b,
            ‖matterCoordinateEquiv
              (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
                space)‖ ^ 2) := by
      rw [← mul_assoc, inv_mul_cancel₀ κPositive.ne', one_mul]
    _ ≤ κ⁻¹ *
        (‖galerkinWeakEnergy
            (fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact)
            coefficient timeStart‖ *
          Real.exp (K * (time - timeStart))) :=
      mul_le_mul_of_nonneg_left scaledL2Bound
        (inv_nonneg.mpr κPositive.le)

/-- A common initial energy cap bounds every fixed-test weak pairing uniformly
in the finite Galerkin carrier and in time. -/
theorem exists_fixedModeUniformGalerkinWeakTestPairingUniformBoundOnBox
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (coefficient velocity : ℝ →
          DiracMatterGalerkinCoefficient candidateModeCount)
        (test : DiracMatterGalerkinCoefficient candidateModeCount),
        (∀ time ∈ Icc timeStart timeEnd,
          HasDerivWithinAt coefficient (velocity time)
            (Icc timeStart timeEnd) time) →
        (∀ time ∈ Icc timeStart timeEnd,
          ∀ candidateTest : DiracMatterGalerkinCoefficient candidateModeCount,
            fixedP506L0CauchySafeMatterWeakMassForm basis
                (fun mode ↦ (basisRegular mode).continuous) basisCompact time
                (velocity time) candidateTest +
              fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
                basisCompact time (coefficient time) candidateTest = 0) →
        (testCoordinates = fun point ↦
          matterCoordinateEquiv
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point)) →
        ‖galerkinWeakEnergy
            (fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact)
            coefficient timeStart‖ ≤ energyCap →
        ∀ time ∈ Icc timeStart timeEnd,
          ‖galerkinWeakTestPairing
              (fixedP506L0CauchySafeMatterWeakMassForm basis
                (fun mode ↦ (basisRegular mode).continuous) basisCompact)
              coefficient test time‖ ≤ B := by
  obtain ⟨C, CNonnegative, pairingBound⟩ :=
    exists_fixedModeUniformGalerkinWeakTestPairingBoundOnBox
      testCoordinates testRegular timeStart timeEnd a b timeOrder boxOrder
  obtain ⟨κ, K, κPositive, KNonnegative, spatialL2Bound⟩ :=
    exists_fixedModeUniformGalerkinSpatialL2BoundOnBox
      timeStart timeEnd a b timeOrder boxOrder
  let B : ℝ := C *
    (κ⁻¹ * (energyCap * Real.exp (K * (timeEnd - timeStart))) +
      volume.real (Icc a b))
  have BNonnegative : 0 ≤ B := by
    exact mul_nonneg CNonnegative
      (add_nonneg
        (mul_nonneg (inv_nonneg.mpr κPositive.le)
          (mul_nonneg energyCapNonnegative (Real.exp_nonneg _)))
        measureReal_nonneg)
  refine ⟨B, BNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient velocity test evolution weakEquation testRepresentation
    initialEnergyBound time timeMem
  have selfWeakEquation : ∀ candidateTime ∈ Icc timeStart timeEnd,
      fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact candidateTime
          (velocity candidateTime) (coefficient candidateTime) +
        fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact candidateTime (coefficient candidateTime)
            (coefficient candidateTime) = 0 := by
    intro candidateTime candidateTimeMem
    exact weakEquation candidateTime candidateTimeMem
      (coefficient candidateTime)
  have generatedPairingBound := pairingBound candidateModeCount basis
    basisRegular basisCompact basisZeroOutside coefficient test
    testRepresentation time timeMem
  have generatedL2Bound := spatialL2Bound candidateModeCount basis basisRegular
    basisCompact basisZeroOutside coefficient velocity evolution
    selfWeakEquation time timeMem
  have exponentBound :
      Real.exp (K * (time - timeStart)) ≤
        Real.exp (K * (timeEnd - timeStart)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right timeMem.2 timeStart) KNonnegative
  have energyEnvelope :
      ‖galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient timeStart‖ * Real.exp (K * (time - timeStart)) ≤
        energyCap * Real.exp (K * (timeEnd - timeStart)) :=
    mul_le_mul initialEnergyBound exponentBound (Real.exp_nonneg _)
      energyCapNonnegative
  have l2Envelope :
      (∫ space in Icc a b,
          ‖matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
              space)‖ ^ 2) ≤
        κ⁻¹ * (energyCap * Real.exp (K * (timeEnd - timeStart))) :=
    generatedL2Bound.trans
      (mul_le_mul_of_nonneg_left energyEnvelope
        (inv_nonneg.mpr κPositive.le))
  exact generatedPairingBound.trans
    (mul_le_mul_of_nonneg_left
      (by
        simpa [add_comm] using
          add_le_add_right l2Envelope (volume.real (Icc a b)))
      CNonnegative)

/-- A common initial energy cap bounds every fixed-test weak rate uniformly
in the finite Galerkin carrier and in time. -/
theorem exists_fixedModeUniformGalerkinWeakTestPairingRateUniformBoundOnBox
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (coefficient velocity : ℝ →
          DiracMatterGalerkinCoefficient candidateModeCount)
        (test : DiracMatterGalerkinCoefficient candidateModeCount),
        (∀ time ∈ Icc timeStart timeEnd,
          HasDerivWithinAt coefficient (velocity time)
            (Icc timeStart timeEnd) time) →
        (∀ time ∈ Icc timeStart timeEnd,
          ∀ candidateTest : DiracMatterGalerkinCoefficient candidateModeCount,
            fixedP506L0CauchySafeMatterWeakMassForm basis
                (fun mode ↦ (basisRegular mode).continuous) basisCompact time
                (velocity time) candidateTest +
              fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
                basisCompact time (coefficient time) candidateTest = 0) →
        (testCoordinates = fun point ↦
          matterCoordinateEquiv
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point)) →
        ‖galerkinWeakEnergy
            (fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact)
            coefficient timeStart‖ ≤ energyCap →
        ∀ time ∈ Icc timeStart timeEnd,
          ‖galerkinWeakTestPairingRate
              (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis
                basisRegular basisCompact)
              (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
                basisCompact)
              coefficient test time‖ ≤ L := by
  obtain ⟨C, CNonnegative, rateBound⟩ :=
    exists_fixedModeUniformGalerkinWeakTestPairingRateBoundOnBox
      testCoordinates testRegular timeStart timeEnd a b timeOrder boxOrder
  obtain ⟨κ, K, κPositive, KNonnegative, spatialL2Bound⟩ :=
    exists_fixedModeUniformGalerkinSpatialL2BoundOnBox
      timeStart timeEnd a b timeOrder boxOrder
  let L : ℝ := C *
    (κ⁻¹ * (energyCap * Real.exp (K * (timeEnd - timeStart))) +
      volume.real (Icc a b))
  have LNonnegative : 0 ≤ L := by
    exact mul_nonneg CNonnegative
      (add_nonneg
        (mul_nonneg (inv_nonneg.mpr κPositive.le)
          (mul_nonneg energyCapNonnegative (Real.exp_nonneg _)))
        measureReal_nonneg)
  refine ⟨L, LNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient velocity test evolution weakEquation testRepresentation
    initialEnergyBound time timeMem
  have selfWeakEquation : ∀ candidateTime ∈ Icc timeStart timeEnd,
      fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact candidateTime
          (velocity candidateTime) (coefficient candidateTime) +
        fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact candidateTime (coefficient candidateTime)
            (coefficient candidateTime) = 0 := by
    intro candidateTime candidateTimeMem
    exact weakEquation candidateTime candidateTimeMem
      (coefficient candidateTime)
  have spatialL2 := spatialL2Bound candidateModeCount basis basisRegular
    basisCompact basisZeroOutside coefficient velocity evolution
    selfWeakEquation
  have generatedRateBound := rateBound candidateModeCount basis basisRegular
    basisCompact basisZeroOutside coefficient test testRepresentation time
    timeMem
  have generatedL2Bound := spatialL2 time timeMem
  have exponentBound :
      Real.exp (K * (time - timeStart)) ≤
        Real.exp (K * (timeEnd - timeStart)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right timeMem.2 timeStart) KNonnegative
  have energyEnvelope :
      ‖galerkinWeakEnergy
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient timeStart‖ * Real.exp (K * (time - timeStart)) ≤
        energyCap * Real.exp (K * (timeEnd - timeStart)) :=
    mul_le_mul initialEnergyBound exponentBound (Real.exp_nonneg _)
      energyCapNonnegative
  have l2Envelope :
      (∫ space in Icc a b,
          ‖matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
              space)‖ ^ 2) ≤
        κ⁻¹ * (energyCap * Real.exp (K * (timeEnd - timeStart))) :=
    generatedL2Bound.trans
      (mul_le_mul_of_nonneg_left energyEnvelope
        (inv_nonneg.mpr κPositive.le))
  exact generatedRateBound.trans
    (mul_le_mul_of_nonneg_left
      (by
        simpa [add_comm] using
          add_le_add_right l2Envelope (volume.real (Icc a b)))
      CNonnegative)

/-- A common initial energy cap makes every fixed-test weak pairing uniformly
Lipschitz in time, independently of the finite Galerkin carrier. -/
theorem exists_fixedModeUniformGalerkinWeakTestPairingLipschitzOnBox
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (candidateModeCount : ℕ)
        (basis : Fin candidateModeCount →
          DiracMatterSpatialCoordinates → ℝ)
        (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
        (basisCompact : ∀ mode, HasCompactSupport (basis mode))
        (_basisZeroOutside :
          DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
        (coefficient velocity : ℝ →
          DiracMatterGalerkinCoefficient candidateModeCount)
        (test : DiracMatterGalerkinCoefficient candidateModeCount),
        (∀ time ∈ Icc timeStart timeEnd,
          HasDerivWithinAt coefficient (velocity time)
            (Icc timeStart timeEnd) time) →
        (∀ time ∈ Icc timeStart timeEnd,
          ∀ candidateTest : DiracMatterGalerkinCoefficient candidateModeCount,
            fixedP506L0CauchySafeMatterWeakMassForm basis
                (fun mode ↦ (basisRegular mode).continuous) basisCompact time
                (velocity time) candidateTest +
              fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
                basisCompact time (coefficient time) candidateTest = 0) →
        (testCoordinates = fun point ↦
          matterCoordinateEquiv
            (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point)) →
        ‖galerkinWeakEnergy
            (fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact)
            coefficient timeStart‖ ≤ energyCap →
        ∀ firstTime ∈ Icc timeStart timeEnd,
          ∀ secondTime ∈ Icc timeStart timeEnd,
            ‖galerkinWeakTestPairing
                (fixedP506L0CauchySafeMatterWeakMassForm basis
                  (fun mode ↦ (basisRegular mode).continuous) basisCompact)
                coefficient test secondTime -
              galerkinWeakTestPairing
                (fixedP506L0CauchySafeMatterWeakMassForm basis
                  (fun mode ↦ (basisRegular mode).continuous) basisCompact)
                coefficient test firstTime‖ ≤
              L * ‖secondTime - firstTime‖ := by
  obtain ⟨L, LNonnegative, rateBound⟩ :=
    exists_fixedModeUniformGalerkinWeakTestPairingRateUniformBoundOnBox
      testCoordinates testRegular timeStart timeEnd a b timeOrder boxOrder
      energyCap energyCapNonnegative
  refine ⟨L, LNonnegative, ?_⟩
  intro candidateModeCount basis basisRegular basisCompact basisZeroOutside
    coefficient velocity test evolution weakEquation testRepresentation
    initialEnergyBound firstTime firstTimeMem secondTime secondTimeMem
  have pairingDerivative : ∀ time ∈ Icc timeStart timeEnd,
      HasDerivWithinAt
        (galerkinWeakTestPairing
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient test)
        (galerkinWeakTestPairingRate
          (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
            basisCompact)
          (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
            basisCompact)
          coefficient test time)
        (Icc timeStart timeEnd) time := by
    intro time timeMem
    exact galerkinWeakTestPairing_hasDerivWithinAt
      (fixedP506L0CauchySafeMatterWeakMassForm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
      (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
        basisCompact)
      (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
        basisCompact)
      coefficient (velocity time) test (Icc timeStart timeEnd) time
      (fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt basis basisRegular
        basisCompact time).hasDerivWithinAt
      (evolution time timeMem)
      (weakEquation time timeMem test)
  have pairingRateBound : ∀ time ∈ Icc timeStart timeEnd,
      ‖galerkinWeakTestPairingRate
          (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
            basisCompact)
          (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
            basisCompact)
          coefficient test time‖ ≤ L := by
    exact rateBound candidateModeCount basis basisRegular basisCompact
      basisZeroOutside coefficient velocity test evolution weakEquation
      testRepresentation initialEnergyBound
  exact (convex_Icc timeStart timeEnd).norm_image_sub_le_of_norm_hasDerivWithin_le
    pairingDerivative pairingRateBound firstTimeMem secondTimeMem

private theorem fixedWeakTestPointwiseGreenRate_add
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates)
    (first second : DiracMatterGalerkinCoefficient 1) :
    fixedWeakTestPointwiseGreenRate testCoordinates point (first + second) =
      fixedWeakTestPointwiseGreenRate testCoordinates point first +
        fixedWeakTestPointwiseGreenRate testCoordinates point second := by
  unfold fixedWeakTestPointwiseGreenRate
  simp only [map_add, add_apply, Finset.sum_add_distrib]
  ring

private def fixedWeakTestGreenRateFiberLinear
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates) :
    MatterCoordinateCarrier →ₗ[ℝ] ℝ where
  toFun trialCoordinates :=
    fixedWeakTestPointwiseGreenRate testCoordinates point
      (fiberCoefficientCLM trialCoordinates)
  map_add' first second := by
    rw [map_add, fixedWeakTestPointwiseGreenRate_add]
  map_smul' parameter trial := by
    rw [map_smul, fixedWeakTestPointwiseGreenRate_real_smul]
    rfl

/-- A smooth spacetime test generates the fiberwise continuous Green-rate
read of the mother action at one spacetime point. -/
def fixedP506L0CauchySafeMatterGreenRateFiberRead
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates) :
    MatterCoordinateCarrier →L[ℝ] ℝ :=
  ⟨fixedWeakTestGreenRateFiberLinear testCoordinates point,
    (fixedWeakTestGreenRateFiberLinear testCoordinates point
      ).continuous_of_finiteDimensional⟩

@[simp] theorem fixedP506L0CauchySafeMatterGreenRateFiberRead_apply
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates)
    (trialCoordinates : MatterCoordinateCarrier) :
    fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates point
        trialCoordinates =
      fixedWeakTestPointwiseGreenRate testCoordinates point
        (fiberCoefficientCLM trialCoordinates) :=
  rfl

/-- The pointwise Green-rate read depends on a spacetime test through its
value and three spatial directional derivatives at the observed point. -/
theorem fixedP506L0CauchySafeMatterGreenRateFiberRead_eq_of_spatialFirstJet_eq
    (first second : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates)
    (valueEq : first (diracMatterSpacetimeCoordinatePoint point.1 point.2) =
      second (diracMatterSpacetimeCoordinatePoint point.1 point.2))
    (derivativeEq : ∀ direction : Fin 3,
      fieldDirectionalDerivative first
          (diracMatterSpacetimeCoordinatePoint point.1 point.2) direction.succ =
        fieldDirectionalDerivative second
          (diracMatterSpacetimeCoordinatePoint point.1 point.2) direction.succ) :
    fixedP506L0CauchySafeMatterGreenRateFiberRead first point =
      fixedP506L0CauchySafeMatterGreenRateFiberRead second point := by
  ext trialCoordinates
  simp only [fixedP506L0CauchySafeMatterGreenRateFiberRead_apply]
  unfold fixedWeakTestPointwiseGreenRate fixedWeakTestValueCoefficient
    fixedWeakTestSpatialDerivativeCoefficient
  rw [valueEq]
  simp_rw [derivativeEq]

local instance greenRateMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-- Fiber carrier containing exactly the value and three spatial derivatives
read by the pointwise Green-rate functional. -/
abbrev CauchySafeMatterSpatialFirstJetFiber :=
  MatterCoordinateCarrier ×
    WithLp 2 (Fin 3 → MatterCoordinateCarrier)

private def fixedWeakSpatialFirstJetGreenRateValue
    (point : ℝ × DiracMatterSpatialCoordinates)
    (jet : CauchySafeMatterSpatialFirstJetFiber)
    (trialCoordinates : MatterCoordinateCarrier) : ℝ :=
    fixedOneModeMassForm
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
          canonicalLorentzianTimeDirection)
        point.1 point.2 (fiberCoefficientCLM trialCoordinates)
        (fiberCoefficientCLM jet.1) -
      fixedOneModeStiffnessForm point.1 point.2
        (fiberCoefficientCLM jet.1) (fiberCoefficientCLM trialCoordinates) +
      ∑ direction : Fin 3,
        fixedOneModeMassForm (fixedEvolutionPrincipalOnSlice direction.succ)
          point.1 point.2 (fiberCoefficientCLM trialCoordinates)
          (fiberCoefficientCLM (jet.2 direction)) +
      ∑ direction : Fin 3,
        fixedOneModeMassForm
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ)
          point.1 point.2 (fiberCoefficientCLM jet.1)
          (fiberCoefficientCLM trialCoordinates)

private theorem fixedWeakSpatialFirstJetGreenRateValue_add_right
    (point : ℝ × DiracMatterSpatialCoordinates)
    (jet : CauchySafeMatterSpatialFirstJetFiber)
    (first second : MatterCoordinateCarrier) :
    fixedWeakSpatialFirstJetGreenRateValue point jet (first + second) =
      fixedWeakSpatialFirstJetGreenRateValue point jet first +
        fixedWeakSpatialFirstJetGreenRateValue point jet second := by
  unfold fixedWeakSpatialFirstJetGreenRateValue
  simp only [map_add, add_apply,
    Finset.sum_add_distrib]
  ring

private theorem fixedWeakSpatialFirstJetGreenRateValue_smul_right
    (point : ℝ × DiracMatterSpatialCoordinates)
    (jet : CauchySafeMatterSpatialFirstJetFiber)
    (parameter : ℝ)
    (trial : MatterCoordinateCarrier) :
    fixedWeakSpatialFirstJetGreenRateValue point jet (parameter • trial) =
      parameter • fixedWeakSpatialFirstJetGreenRateValue point jet trial := by
  unfold fixedWeakSpatialFirstJetGreenRateValue
  simp only [map_smul, smul_apply,
    smul_eq_mul, ← Finset.mul_sum]
  ring

private theorem fixedWeakSpatialFirstJetGreenRateValue_add_left
    (point : ℝ × DiracMatterSpatialCoordinates)
    (first second : CauchySafeMatterSpatialFirstJetFiber)
    (trialCoordinates : MatterCoordinateCarrier) :
    fixedWeakSpatialFirstJetGreenRateValue point (first + second)
        trialCoordinates =
      fixedWeakSpatialFirstJetGreenRateValue point first trialCoordinates +
        fixedWeakSpatialFirstJetGreenRateValue point second trialCoordinates := by
  unfold fixedWeakSpatialFirstJetGreenRateValue
  simp only [Prod.fst_add, Prod.snd_add, WithLp.ofLp_add, Pi.add_apply,
    map_add, add_apply, Finset.sum_add_distrib]
  ring

private theorem fixedWeakSpatialFirstJetGreenRateValue_smul_left
    (point : ℝ × DiracMatterSpatialCoordinates)
    (parameter : ℝ)
    (jet : CauchySafeMatterSpatialFirstJetFiber)
    (trialCoordinates : MatterCoordinateCarrier) :
    fixedWeakSpatialFirstJetGreenRateValue point (parameter • jet)
        trialCoordinates =
      parameter • fixedWeakSpatialFirstJetGreenRateValue point jet
        trialCoordinates := by
  unfold fixedWeakSpatialFirstJetGreenRateValue
  simp only [Prod.smul_fst, Prod.smul_snd, WithLp.ofLp_smul, Pi.smul_apply,
    map_smul, smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

private def fixedWeakSpatialFirstJetGreenRateInnerLinear
    (point : ℝ × DiracMatterSpatialCoordinates)
    (jet : CauchySafeMatterSpatialFirstJetFiber) :
    MatterCoordinateCarrier →ₗ[ℝ] ℝ where
  toFun := fixedWeakSpatialFirstJetGreenRateValue point jet
  map_add' := fixedWeakSpatialFirstJetGreenRateValue_add_right point jet
  map_smul' := fixedWeakSpatialFirstJetGreenRateValue_smul_right point jet

private def fixedWeakSpatialFirstJetGreenRateInnerCLM
    (point : ℝ × DiracMatterSpatialCoordinates)
    (jet : CauchySafeMatterSpatialFirstJetFiber) :
    MatterCoordinateCarrier →L[ℝ] ℝ :=
  ⟨fixedWeakSpatialFirstJetGreenRateInnerLinear point jet,
    (fixedWeakSpatialFirstJetGreenRateInnerLinear point jet
      ).continuous_of_finiteDimensional⟩

private def fixedWeakSpatialFirstJetGreenRateOuterLinear
    (point : ℝ × DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialFirstJetFiber →ₗ[ℝ]
      (MatterCoordinateCarrier →L[ℝ] ℝ) where
  toFun := fixedWeakSpatialFirstJetGreenRateInnerCLM point
  map_add' first second := by
    ext trialCoordinates
    exact fixedWeakSpatialFirstJetGreenRateValue_add_left point first second
      trialCoordinates
  map_smul' parameter jet := by
    ext trialCoordinates
    exact fixedWeakSpatialFirstJetGreenRateValue_smul_left point parameter jet
      trialCoordinates

/-- At each spacetime point, the mother-action Green rate is a continuous
linear read of the finite spatial first jet of its test. -/
def fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead
    (point : ℝ × DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
      (MatterCoordinateCarrier →L[ℝ] ℝ) :=
  ⟨fixedWeakSpatialFirstJetGreenRateOuterLinear point,
    (fixedWeakSpatialFirstJetGreenRateOuterLinear point
      ).continuous_of_finiteDimensional⟩

@[simp] theorem
    fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead_apply
    (point : ℝ × DiracMatterSpatialCoordinates)
    (jet : CauchySafeMatterSpatialFirstJetFiber)
    (trialCoordinates : MatterCoordinateCarrier) :
    fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead point jet
        trialCoordinates =
      fixedOneModeMassForm
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection)
          point.1 point.2 (fiberCoefficientCLM trialCoordinates)
          (fiberCoefficientCLM jet.1) -
        fixedOneModeStiffnessForm point.1 point.2
          (fiberCoefficientCLM jet.1) (fiberCoefficientCLM trialCoordinates) +
        ∑ direction : Fin 3,
          fixedOneModeMassForm (fixedEvolutionPrincipalOnSlice direction.succ)
            point.1 point.2 (fiberCoefficientCLM trialCoordinates)
            (fiberCoefficientCLM (jet.2 direction)) +
        ∑ direction : Fin 3,
          fixedOneModeMassForm
            (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
              direction.succ)
            point.1 point.2 (fiberCoefficientCLM jet.1)
            (fiberCoefficientCLM trialCoordinates) :=
  rfl

theorem fixedP506L0CauchySafeMatterGreenRateFiberRead_eq_spatialFirstJetRead
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (point : ℝ × DiracMatterSpatialCoordinates) :
    fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates point =
      fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead point
        (testCoordinates
            (diracMatterSpacetimeCoordinatePoint point.1 point.2),
          WithLp.toLp 2 fun spatialDirection ↦
            fieldDirectionalDerivative testCoordinates
              (diracMatterSpacetimeCoordinatePoint point.1 point.2)
              spatialDirection.succ) := by
  ext trialCoordinates
  rfl

theorem
    fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead_continuous :
    Continuous fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead := by
  rw [continuous_clm_apply]
  intro jet
  rw [continuous_clm_apply]
  intro trialCoordinates
  have temporalTermContinuous : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates ↦
      fixedOneModeMassForm
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection)
          point.1 point.2 (fiberCoefficientCLM trialCoordinates)
          (fiberCoefficientCLM jet.1)) :=
    ((fixedOneModeMassForm_continuous
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection)
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
        canonicalLorentzianTimeDirection)).clm_apply continuous_const
      ).clm_apply continuous_const
  have stiffnessTermContinuous : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates ↦
      fixedOneModeStiffnessForm point.1 point.2
        (fiberCoefficientCLM jet.1)
        (fiberCoefficientCLM trialCoordinates)) :=
    (fixedOneModeStiffnessForm_continuous.clm_apply continuous_const
      ).clm_apply continuous_const
  have principalTermContinuous (direction : Fin 3) : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates ↦
      fixedOneModeMassForm (fixedEvolutionPrincipalOnSlice direction.succ)
        point.1 point.2 (fiberCoefficientCLM trialCoordinates)
        (fiberCoefficientCLM (jet.2 direction))) := by
    exact ((fixedOneModeMassForm_continuous
      (fixedEvolutionPrincipalOnSlice direction.succ)
      (fun row column ↦
        (fixedEvolutionPrincipalOnSlice_entry_contDiff direction.succ row column
          ).continuous)).clm_apply continuous_const).clm_apply continuous_const
  have derivativeTermContinuous (direction : Fin 3) : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates ↦
      fixedOneModeMassForm
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ)
          point.1 point.2 (fiberCoefficientCLM jet.1)
          (fiberCoefficientCLM trialCoordinates)) := by
    exact ((fixedOneModeMassForm_continuous
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice direction.succ)
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
        direction.succ)).clm_apply continuous_const).clm_apply continuous_const
  change Continuous (fun point : ℝ × DiracMatterSpatialCoordinates ↦
    fixedWeakSpatialFirstJetGreenRateValue point jet trialCoordinates)
  unfold fixedWeakSpatialFirstJetGreenRateValue
  convert
    ((temporalTermContinuous.sub stiffnessTermContinuous).add
      ((continuous_finsetSum Finset.univ fun direction _ ↦
        principalTermContinuous direction).add
        (continuous_finsetSum Finset.univ fun direction _ ↦
          derivativeTermContinuous direction))) using 1
  funext point
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem fixedP506L0CauchySafeMatterGreenRateFiberRead_apply_continuous
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (trialCoordinates : MatterCoordinateCarrier) :
    Continuous (fun point : ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates point
        trialCoordinates) := by
  change Continuous (fun point : ℝ × DiracMatterSpatialCoordinates ↦
    fixedWeakTestPointwiseGreenRate testCoordinates point
      (fiberCoefficientCLM trialCoordinates))
  let inputPath : ℝ × DiracMatterSpatialCoordinates →
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 :=
    fun point ↦ (point, fiberCoefficientCLM trialCoordinates)
  have inputPathContinuous : Continuous inputPath :=
    continuous_id.prodMk continuous_const
  change Continuous ((fun input :
      (ℝ × DiracMatterSpatialCoordinates) ×
        DiracMatterGalerkinCoefficient 1 ↦
    fixedWeakTestPointwiseGreenRate testCoordinates input.1 input.2) ∘
      inputPath)
  exact (fixedWeakTestPointwiseGreenRate_joint_continuous testCoordinates
    testRegular).comp inputPathContinuous

/-- Green transport identifies the finite weak-pairing rate with the
fiberwise action read on the varying Galerkin trial field. -/
theorem fixedP506L0CauchySafeMatterGalerkinWeakTestPairingRate_eq_greenRead
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (trial : ℝ → DiracMatterGalerkinCoefficient candidateModeCount)
    (test : DiracMatterGalerkinCoefficient candidateModeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    galerkinWeakTestPairingRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
          basisCompact)
        (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
          basisCompact)
        trial test time =
      ∫ space in Icc a b,
        fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates
          (time, space)
          (matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis basis (trial time) space)) := by
  rw [fixedGalerkinWeakTestPairingRate_eq_box_green basis basisRegular
    basisCompact trial test time a b boxOrder basisZeroOutside]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun space ↦ by
    rw [fixedWeakTestGreenRateDensity_eq_pointwise basis (trial time) test
      testCoordinates testRepresentation time space]
    change fixedWeakTestPointwiseGreenRate testCoordinates (time, space)
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis basis (trial time) space)) =
      fixedWeakTestPointwiseGreenRate testCoordinates (time, space)
        (fiberCoefficientCLM
          (matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis basis (trial time) space)))
    rw [← fiberCoefficient_eq_clm]

/-! ## Constant affine-lift Green assembly -/

/-- Mother-action velocity of a spacetime-constant matter field.  This is the
fixed affine-lift leg before any finite Galerkin carrier is selected. -/
def fixedP506L0CauchySafeMatterConstantFieldActionResponse
    (field : DiracExteriorMatterCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  cauchySafeMatterVolterraVelocity FixedCurrent (fun _point ↦ field)
    (diracMatterSpacetimeCoordinatePoint time space)

theorem fixedP506L0CauchySafeMatterConstantFieldActionResponse_eq_fixedConstant
    (field : DiracExteriorMatterCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    fixedP506L0CauchySafeMatterConstantFieldActionResponse field time space =
      fixedConstantActionResponse time
        (WithLp.toLp 2 fun index ↦ matterCoordinateEquiv field index.2) space := by
  exact (fixedConstantActionResponse_fiberCoefficient time space field).symm

private def constantHeadBasis
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ) :
    Fin (candidateModeCount + 1) → DiracMatterSpatialCoordinates → ℝ :=
  Fin.cases (fun _space ↦ 1) basis

private def constantHeadCoefficient
    {candidateModeCount : ℕ}
    (field : DiracExteriorMatterCarrier) :
    DiracMatterGalerkinCoefficient (candidateModeCount + 1) :=
  WithLp.toLp 2 fun index ↦
    Fin.cases (matterCoordinateEquiv field index.2) (fun _mode ↦ 0) index.1

private def constantHeadTailCoefficient
    {candidateModeCount : ℕ}
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount) :
    DiracMatterGalerkinCoefficient (candidateModeCount + 1) :=
  WithLp.toLp 2 fun index ↦
    Fin.cases 0 (fun mode ↦ coefficient (mode, index.2)) index.1

@[simp] private theorem constantHeadCoefficient_mode_zero
    {candidateModeCount : ℕ}
    (field : DiracExteriorMatterCarrier) :
    diracMatterGalerkinCoefficientMode
        (constantHeadCoefficient (candidateModeCount := candidateModeCount)
          field) 0 =
      matterCoordinateEquiv field := by
  ext coordinate
  rfl

@[simp] private theorem constantHeadCoefficient_mode_succ
    {candidateModeCount : ℕ}
    (field : DiracExteriorMatterCarrier)
    (mode : Fin candidateModeCount) :
    diracMatterGalerkinCoefficientMode
        (constantHeadCoefficient (candidateModeCount := candidateModeCount)
          field) mode.succ = 0 := by
  ext coordinate
  rfl

@[simp] private theorem constantHeadTailCoefficient_mode_zero
    {candidateModeCount : ℕ}
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount) :
    diracMatterGalerkinCoefficientMode
        (constantHeadTailCoefficient coefficient) 0 = 0 := by
  ext coordinate
  rfl

@[simp] private theorem constantHeadTailCoefficient_mode_succ
    {candidateModeCount : ℕ}
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (mode : Fin candidateModeCount) :
    diracMatterGalerkinCoefficientMode
        (constantHeadTailCoefficient coefficient) mode.succ =
      diracMatterGalerkinCoefficientMode coefficient mode := by
  ext coordinate
  rfl

private theorem constantHeadCoefficient_synthesis
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (field : DiracExteriorMatterCarrier)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialGalerkinSynthesis (constantHeadBasis basis)
        (constantHeadCoefficient field) space = field := by
  apply matterCoordinateEquiv.injective
  rw [diracMatterSpatialGalerkinSynthesis_coordinates, Fin.sum_univ_succ]
  simp [constantHeadBasis]

private theorem constantHeadTailCoefficient_synthesis
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient candidateModeCount)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialGalerkinSynthesis (constantHeadBasis basis)
        (constantHeadTailCoefficient coefficient) space =
      diracMatterSpatialGalerkinSynthesis basis coefficient space := by
  apply matterCoordinateEquiv.injective
  rw [diracMatterSpatialGalerkinSynthesis_coordinates,
    diracMatterSpatialGalerkinSynthesis_coordinates, Fin.sum_univ_succ]
  simp [constantHeadBasis]

/-- Green transport for a fixed spacetime-constant affine lift.  The only
extra term beyond its action velocity is the time derivative of the dynamic
mother-action mass form. -/
theorem fixedP506L0CauchySafeMatterGreenRateFiberRead_constantField_box
    {candidateModeCount : ℕ}
    (basis : Fin candidateModeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (test : DiracMatterGalerkinCoefficient candidateModeCount)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test point))
    (field : DiracExteriorMatterCarrier)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b) :
    (∫ space in Icc a b,
        fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates
          (time, space) (matterCoordinateEquiv field)) =
      (∫ space in Icc a b,
        diracExteriorMatterEnergyPairing
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection time space)
          field
          (matterCoordinateEquiv.symm
            (testCoordinates
              (diracMatterSpacetimeCoordinatePoint time space)))) -
        diracMatterWeakStiffnessFormValue
          (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
          (fun _coefficient space ↦
            fixedP506L0CauchySafeMatterConstantFieldActionResponse
              field time space)
          test 0 := by
  let extendedBasis := constantHeadBasis basis
  let liftCoefficient : DiracMatterGalerkinCoefficient
      (candidateModeCount + 1) := constantHeadCoefficient field
  let extendedTest : DiracMatterGalerkinCoefficient
      (candidateModeCount + 1) := constantHeadTailCoefficient test
  have extendedBasisRegular : ∀ mode, ContDiff ℝ 1 (extendedBasis mode) := by
    intro mode
    refine Fin.cases ?_ (fun originalMode ↦ ?_) mode
    · exact contDiff_const
    · exact basisRegular originalMode
  have liftCandidateEq :
      fixedP506L0CauchySafeMatterWeakSpatialCandidate
          extendedBasis liftCoefficient = fun _point ↦ field := by
    funext point
    apply matterCoordinateEquiv.injective
    simp [fixedP506L0CauchySafeMatterWeakSpatialCandidate,
      cauchySafeMatterGalerkinSynthesis_coordinates,
      fixedP506L0CauchySafeMatterWeakSpatialBasisLift,
      extendedBasis, liftCoefficient, constantHeadBasis,
      constantHeadCoefficient_mode_zero,
      constantHeadCoefficient_mode_succ, Fin.sum_univ_succ]
  have testCandidateEq :
      fixedP506L0CauchySafeMatterWeakSpatialCandidate
          extendedBasis extendedTest =
        fixedP506L0CauchySafeMatterWeakSpatialCandidate basis test := by
    funext point
    apply matterCoordinateEquiv.injective
    simp [fixedP506L0CauchySafeMatterWeakSpatialCandidate,
      cauchySafeMatterGalerkinSynthesis_coordinates,
      fixedP506L0CauchySafeMatterWeakSpatialBasisLift,
      extendedBasis, extendedTest, constantHeadBasis,
      constantHeadTailCoefficient_mode_zero,
      constantHeadTailCoefficient_mode_succ, Fin.sum_univ_succ]
  have extendedTestRepresentation : testCoordinates = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate
          extendedBasis extendedTest point) := by
    rw [testCandidateEq]
    exact testRepresentation
  let massDensity : DiracMatterSpatialCoordinates → ℝ := fun space ↦
    diracMatterWeakMassDensity
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection time)
      extendedBasis liftCoefficient extendedTest space
  let stiffnessDensity : DiracMatterSpatialCoordinates → ℝ := fun space ↦
    diracMatterWeakStiffnessDensity
      (fixedP506L0CauchySafeMatterWeakMassMatrix time)
      extendedBasis
      (fixedP506L0CauchySafeMatterWeakActionResponse extendedBasis time)
      extendedTest liftCoefficient space
  let greenCombination : DiracMatterSpatialCoordinates → ℝ := fun space ↦
    spatialBilinearPrincipalPairing
        extendedBasis liftCoefficient extendedTest time space +
      spatialBilinearPrincipalPairing
        extendedBasis extendedTest liftCoefficient time space +
      ∑ direction : Fin 3,
        diracMatterWeakMassDensity
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            direction.succ time)
          extendedBasis extendedTest liftCoefficient space
  have liftSpatialDerivativeZero
      (point : BasePoint)
      (direction : LorentzianIndex) :
      rawDirectionalDerivative
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            extendedBasis liftCoefficient)
          point direction = 0 := by
    rw [liftCandidateEq]
    unfold rawDirectionalDerivative fieldDirectionalDerivative
    simp
  have liftSpatialPairingZero (space : DiracMatterSpatialCoordinates) :
      spatialBilinearPrincipalPairing
          extendedBasis extendedTest liftCoefficient time space = 0 := by
    unfold spatialBilinearPrincipalPairing
    dsimp only
    apply Finset.sum_eq_zero
    intro direction _
    rw [liftSpatialDerivativeZero]
    simp [diracMatterBilinearFlux,
      diracExteriorMatterCoordinatePairing, dotProduct]
  have actionResponseEq (space : DiracMatterSpatialCoordinates) :
      fixedP506L0CauchySafeMatterWeakActionResponse extendedBasis time
          liftCoefficient space =
        fixedP506L0CauchySafeMatterConstantFieldActionResponse
          field time space := by
    unfold fixedP506L0CauchySafeMatterWeakActionResponse
      fixedP506L0CauchySafeMatterConstantFieldActionResponse
    rw [liftCandidateEq]
  have massDensityEq (space : DiracMatterSpatialCoordinates) :
      massDensity space =
        diracExteriorMatterEnergyPairing
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection time space)
          field
          (matterCoordinateEquiv.symm
            (testCoordinates
              (diracMatterSpacetimeCoordinatePoint time space))) := by
    have represented := congrFun testRepresentation
      (diracMatterSpacetimeCoordinatePoint time space)
    rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice] at represented
    unfold massDensity diracMatterWeakMassDensity
    rw [constantHeadCoefficient_synthesis,
      constantHeadTailCoefficient_synthesis]
    have representedCarrier := congrArg matterCoordinateEquiv.symm represented
    rw [matterCoordinateEquiv.symm_apply_apply] at representedCarrier
    rw [representedCarrier]
  have stiffnessDensityEq (space : DiracMatterSpatialCoordinates) :
      stiffnessDensity space =
        diracMatterWeakStiffnessDensity
          (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
          (fun _coefficient candidateSpace ↦
            fixedP506L0CauchySafeMatterConstantFieldActionResponse
              field time candidateSpace)
          test 0 space := by
    unfold stiffnessDensity diracMatterWeakStiffnessDensity
    rw [constantHeadTailCoefficient_synthesis, actionResponseEq]
  have greenReadEq (space : DiracMatterSpatialCoordinates) :
      fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates
          (time, space) (matterCoordinateEquiv field) =
        fixedWeakTestGreenRateDensity extendedBasis liftCoefficient
          extendedTest time space := by
    rw [fixedWeakTestGreenRateDensity_eq_pointwise extendedBasis
      liftCoefficient extendedTest testCoordinates
      extendedTestRepresentation time space]
    change fixedWeakTestPointwiseGreenRate testCoordinates (time, space)
        (fiberCoefficientCLM (matterCoordinateEquiv field)) =
      fixedWeakTestPointwiseGreenRate testCoordinates (time, space)
        (fiberCoefficient
          (diracMatterSpatialGalerkinSynthesis extendedBasis liftCoefficient
            space))
    rw [constantHeadCoefficient_synthesis, fiberCoefficient_eq_clm]
  have greenPointwise (space : DiracMatterSpatialCoordinates) :
      fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates
          (time, space) (matterCoordinateEquiv field) =
        (massDensity space - stiffnessDensity space) +
          greenCombination space := by
    rw [greenReadEq]
    unfold fixedWeakTestGreenRateDensity massDensity stiffnessDensity
      greenCombination
    rw [fixedWeakStiffnessDensity_eq_constant_add_bilinearPrincipal
      extendedBasis extendedBasisRegular extendedTest liftCoefficient
      time space]
    rw [liftSpatialPairingZero]
    ring
  let flux := diracMatterSpatialBilinearFlux fixedEvolutionPrincipal
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate
      extendedBasis extendedTest)
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate
      extendedBasis liftCoefficient)
    time
  have fluxRegular : ∀ direction : Fin 3, ContDiff ℝ 1 (flux direction) :=
    fun direction ↦
      fixedSpatialBilinearFlux_contDiff_one extendedBasis
        extendedBasisRegular extendedTest liftCoefficient time direction
  have fluxBoundaryZero : DiracMatterSpatialFluxZeroOnBoxBoundary flux a b := by
    intro direction point _pointMem
    have frontOutside : ¬ DiracMatterSpatialBoxInterior a b
        (direction.insertNth (b direction) point) := by
      intro frontInterior
      have strict := (frontInterior direction).2
      simpa using strict
    have backOutside : ¬ DiracMatterSpatialBoxInterior a b
        (direction.insertNth (a direction) point) := by
      intro backInterior
      have strict := (backInterior direction).1
      simpa using strict
    have frontZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
      test a b basisZeroOutside
      (direction.insertNth (b direction) point) frontOutside
    have backZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
      test a b basisZeroOutside
      (direction.insertNth (a direction) point) backOutside
    constructor
    · simp only [flux, diracMatterSpatialBilinearFlux]
      rw [testCandidateEq,
        fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice, frontZero]
      simp [diracMatterBilinearFlux,
        diracExteriorMatterCoordinatePairing, dotProduct]
    · simp only [flux, diracMatterSpatialBilinearFlux]
      rw [testCandidateEq,
        fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice, backZero]
      simp [diracMatterBilinearFlux,
        diracExteriorMatterCoordinatePairing, dotProduct]
  have greenDivergenceEq : greenCombination =
      diracMatterSpatialFluxDivergence flux := by
    funext space
    exact (fixedSpatialBilinearFluxDivergence_eq extendedBasis
      extendedBasisRegular extendedTest liftCoefficient time space).symm
  have greenIntegrable : IntegrableOn greenCombination (Icc a b) := by
    rw [greenDivergenceEq]
    exact (diracMatterSpatialFluxDivergence_continuous flux fluxRegular
      ).continuousOn.integrableOn_compact isCompact_Icc
  have greenIntegralZero :
      (∫ space in Icc a b, greenCombination space) = 0 := by
    rw [greenDivergenceEq]
    exact integral_diracMatterSpatialFluxDivergence_box_eq_zero
      flux a b boxOrder fluxRegular fluxBoundaryZero
  have massContinuous : Continuous massDensity := by
    exact diracMatterWeakMassDensity_continuous
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection time)
      extendedBasis
      (fun row column ↦
        (fixedEvolutionPrincipalDirectionalDerivativeOnSlice_entry_continuous
          canonicalLorentzianTimeDirection row column).comp
          (continuous_const.prodMk continuous_id))
      (fun mode ↦ (extendedBasisRegular mode).continuous)
      liftCoefficient extendedTest
  have stiffnessContinuous : Continuous stiffnessDensity := by
    exact fixedWeakStiffnessDensity_bilinear_continuous extendedBasis
      extendedBasisRegular extendedTest liftCoefficient time
  have originalIntegrable : IntegrableOn
      (fun space ↦ massDensity space - stiffnessDensity space) (Icc a b) :=
    massContinuous.continuousOn.integrableOn_compact isCompact_Icc |>.sub
      (stiffnessContinuous.continuousOn.integrableOn_compact isCompact_Icc)
  have stiffnessZeroOutside (space : DiracMatterSpatialCoordinates)
      (spaceOutside : space ∉ Icc a b) : stiffnessDensity space = 0 := by
    rw [stiffnessDensityEq]
    have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
      intro spaceInterior
      apply spaceOutside
      constructor
      · intro direction
        exact (spaceInterior direction).1.le
      · intro direction
        exact (spaceInterior direction).2.le
    have testZero := spatialSynthesis_eq_zero_of_not_mem_boxInterior basis
      test a b basisZeroOutside space outsideInterior
    unfold diracMatterWeakStiffnessDensity
    rw [testZero]
    simp [diracExteriorMatterEnergyPairing,
      diracExteriorMatterCoordinatePairing, dotProduct]
  have stiffnessSetIntegralEq :
      (∫ space in Icc a b, stiffnessDensity space) =
        ∫ space, stiffnessDensity space :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun space spaceOutside ↦
      stiffnessZeroOutside space spaceOutside)
  have stiffnessFormEq :
      (∫ space, stiffnessDensity space) =
        diracMatterWeakStiffnessFormValue
          (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
          (fun _coefficient space ↦
            fixedP506L0CauchySafeMatterConstantFieldActionResponse
              field time space)
          test 0 := by
    unfold diracMatterWeakStiffnessFormValue
    apply integral_congr_ae
    exact Filter.Eventually.of_forall stiffnessDensityEq
  calc
    (∫ space in Icc a b,
        fixedP506L0CauchySafeMatterGreenRateFiberRead testCoordinates
          (time, space) (matterCoordinateEquiv field)) =
        ∫ space in Icc a b,
          ((massDensity space - stiffnessDensity space) +
            greenCombination space) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro space _
      exact greenPointwise space
    _ = (∫ space in Icc a b,
          (massDensity space - stiffnessDensity space)) +
        ∫ space in Icc a b, greenCombination space :=
      integral_add originalIntegrable greenIntegrable
    _ = ∫ space in Icc a b,
          (massDensity space - stiffnessDensity space) := by
      rw [greenIntegralZero, add_zero]
    _ = (∫ space in Icc a b, massDensity space) -
        ∫ space in Icc a b, stiffnessDensity space :=
      integral_sub
        (massContinuous.continuousOn.integrableOn_compact isCompact_Icc)
        (stiffnessContinuous.continuousOn.integrableOn_compact isCompact_Icc)
    _ = (∫ space in Icc a b,
        diracExteriorMatterEnergyPairing
          (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
            canonicalLorentzianTimeDirection time space)
          field
          (matterCoordinateEquiv.symm
            (testCoordinates
              (diracMatterSpacetimeCoordinatePoint time space)))) -
        diracMatterWeakStiffnessFormValue
          (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
          (fun _coefficient space ↦
            fixedP506L0CauchySafeMatterConstantFieldActionResponse
              field time space)
          test 0 := by
      rw [stiffnessSetIntegralEq, stiffnessFormEq]
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro space _
      exact massDensityEq space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
