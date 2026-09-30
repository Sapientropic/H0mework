import H0mework.NavierStokes.StressResolvent.ResolventEquation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeResolvent

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeSourceResolvent NativeFiniteActionResolvent NativeCommonAdvectorAction NativeRawStressAction
open NativeResolventCompactness NativeEndpointVelocityCarrier

noncomputable section

def wholePhysical : Submodule ℝ State where
  carrier := {value | WholeRestartVelocityEndpointTransverse value ∧ WholeRestartVelocityEndpointReality value}
  zero_mem' := by
    constructor
    · intro wave
      change complexWavevector wave.1 ⬝ᵥ (0 : ComplexCoordinateVector) = 0
      simp
    · intro wave coordinate
      change (0 : ℂ) = star 0
      simp
  add_mem' := by
    intro first last firstPhysical lastPhysical
    constructor
    · intro wave
      change complexWavevector wave.1 ⬝ᵥ ((fun coordinate => first wave coordinate) +
        (fun coordinate => last wave coordinate)) = 0
      rw [dotProduct_add, firstPhysical.1 wave, lastPhysical.1 wave, add_zero]
    · intro wave coordinate
      change first _ coordinate + last _ coordinate = star (first wave coordinate + last wave coordinate)
      rw [firstPhysical.2, lastPhysical.2, star_add]
  smul_mem' := by
    intro scalar value physical
    constructor
    · intro wave
      change complexWavevector wave.1 ⬝ᵥ (scalar • (fun coordinate => value wave coordinate)) = 0
      rw [dotProduct_smul, physical.1 wave, smul_zero]
    · intro wave coordinate
      change scalar • value _ coordinate = star (scalar • value wave coordinate)
      rw [physical.2]
      simp

def coordinateCLM (wave : Wave) (coordinate : Coordinate) : State →L[ℝ] ℂ :=
  ((EuclideanSpace.proj coordinate : ComplexCoordinateEuclidean →L[ℂ] ℂ).restrictScalars ℝ).comp
    (lp.evalCLM ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave)

theorem wholePhysical_closed : IsClosed (wholePhysical : Set State) := by
  have transverse : IsClosed {value : State | WholeRestartVelocityEndpointTransverse value} := by
    simp only [WholeRestartVelocityEndpointTransverse, ofPred_forall]
    apply isClosed_iInter
    intro wave
    apply isClosed_eq _ continuous_const
    exact continuous_const.dotProduct (continuous_pi fun coordinate => (coordinateCLM wave coordinate).continuous)
  have reality : IsClosed {value : State | WholeRestartVelocityEndpointReality value} := by
    simp only [WholeRestartVelocityEndpointReality, ofPred_forall]
    apply isClosed_iInter
    intro wave
    apply isClosed_iInter
    intro coordinate
    exact isClosed_eq (coordinateCLM (nonzeroIntegerWavevectorNeg wave) coordinate).continuous
      (continuous_star.comp (coordinateCLM wave coordinate).continuous)
  exact transverse.inter reality

theorem whole_transverse (value : wholePhysical) (wave : IntegerWavevector) :
    complexWavevector wave ⬝ᵥ wholeVelocity value.1 wave = 0 := by
  by_cases zero : wave = 0
  · subst wave
    simp
  · have same : wholeVelocity value.1 wave = fun coordinate => value.1 ⟨wave, zero⟩ coordinate := by
      funext coordinate
      exact wholeVelocity_nonzero value.1 ⟨wave, zero⟩ coordinate
    rw [same]
    exact value.2.1 ⟨wave, zero⟩

def restrictLoad (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (value : wholePhysical) : physicalSpace frequencies :=
  ofPhysical frequencies zeroNotMem (complexSharpSupportProjection frequencies (wholeVelocity value.1))
    (complexSharpSupportProjection_supported _ _)
    (complexSharpSupportProjection_transverse _ _ (whole_transverse value))
    (complexSharpSupportProjection_reality _ _ closed (wholeVelocity_reality value.1 value.2.2))

def restrictLinear (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) : wholePhysical →ₗ[ℝ] physicalSpace frequencies where
  toFun := restrictLoad frequencies zeroNotMem closed
  map_add' := by
    intro first last
    apply Subtype.ext
    change complexSharpSupportProjection frequencies (wholeVelocityCLM (first.1 + last.1)) =
      complexSharpSupportProjection frequencies (wholeVelocityCLM first.1) +
        complexSharpSupportProjection frequencies (wholeVelocityCLM last.1)
    rw [map_add]
    apply lp.ext
    funext wave
    simp only [lp.coeFn_add, Pi.add_apply, complexSharpSupportProjection_apply]
    split_ifs <;> simp
  map_smul' := by
    intro scalar value
    apply Subtype.ext
    change complexSharpSupportProjection frequencies (wholeVelocityCLM (scalar • value.1)) =
      scalar • complexSharpSupportProjection frequencies (wholeVelocityCLM value.1)
    rw [map_smul]
    apply lp.ext
    funext wave
    simp only [lp.coeFn_smul, Pi.smul_apply, complexSharpSupportProjection_apply]
    split_ifs <;> simp

def restrictCLM (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) : wholePhysical →L[ℝ] physicalSpace frequencies :=
  (restrictLinear frequencies zeroNotMem closed).mkContinuous 1 (fun value => by
    change ‖complexSharpSupportProjection frequencies (wholeVelocity value.1)‖ ≤ 1 * ‖value.1‖
    simpa only [one_mul] using
      (complexSharpSupportProjection_norm_le frequencies (wholeVelocity value.1)).trans (wholeVelocity_norm_le value.1))

theorem restrict_energy (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (closed : FiniteModeNegClosed frequencies) (value : wholePhysical) :
    ‖NativeFiniteActionResolvent.coefficients frequencies (restrictCLM frequencies zeroNotMem closed value)‖ ≤ ‖value‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [coefficients_mass]
  change wholeVorticityEuclideanMass (complexSharpSupportProjection frequencies (wholeVelocity value.1)) ≤ ‖value.1‖ ^ 2
  exact (wholeVorticityEuclideanMass_sharpSupportProjection_le frequencies _).trans_eq (wholeVelocity_mass value.1)

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def stageOperator (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) : wholePhysical →L[ℝ] State :=
  (puncturedEuclideanizeCLM.restrictScalars ℝ).comp ((physicalSpace (modes stress index)).subtypeL.comp
    ((physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
      (advector stress pointLe index node) (advector_reality stress pointLe index node) step nonnegative).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index))))

theorem physical_norm (frequencies : Finset IntegerWavevector) (zeroNotMem : 0 ∉ frequencies)
    (value : physicalSpace frequencies) :
    ‖puncturedEuclideanize value.1‖ = ‖NativeFiniteActionResolvent.coefficients frequencies value‖ := by
  have mass := wholeVelocity_mass (puncturedEuclideanize value.1)
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize value.1
    (physical_supported value 0 zeroNotMem)] at mass
  have coefficientsMass := coefficients_mass frequencies value
  nlinarith [norm_nonneg (puncturedEuclideanize value.1),
    norm_nonneg (NativeFiniteActionResolvent.coefficients frequencies value)]

theorem stage_bound (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) (value : wholePhysical) :
    ‖stageOperator stress pointLe index node step nonnegative value‖ ≤ ‖value‖ := by
  let solved := physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index node) (advector_reality stress pointLe index node) step nonnegative
    (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value)
  change ‖puncturedEuclideanize solved.1‖ ≤ _
  rw [physical_norm (modes stress index) (modes_zero stress index)]
  exact (resolver_contraction (modes stress index) _ (physicalOperator_dissipative _ _ _ _ _ _)
    step nonnegative (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value)).trans
      (restrict_energy _ _ _ value)

theorem stage_contractive (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) : ‖stageOperator stress pointLe index node step nonnegative‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  simpa only [one_mul] using stage_bound stress pointLe index node step nonnegative value

theorem stage_curl_budget (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    Summable (curlDensity (stageOperator stress pointLe index node step positive.le value)) ∧
      (∑' wave, curlDensity (stageOperator stress pointLe index node step positive.le value) wave) ≤
        ‖value‖ ^ 2 / (2 * step * nu.coeff) := by
  let input := restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value
  let solved := physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index node) (advector_reality stress pointLe index node) step positive.le input
  change Summable (curlDensity (puncturedEuclideanize solved.1)) ∧ _
  refine ⟨physical_curl_summable _ solved, ?_⟩
  change (∑' wave, curlDensity (puncturedEuclideanize solved.1) wave) ≤ _
  rw [physical_curl_sum _ (modes_zero stress index)]
  apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) positive) nu.coeff_pos)).mpr
  have balance := physicalResolver_balance (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index node) (advector_reality stress pointLe index node) step positive.le input
  have loadPaid := restrict_energy (modes stress index) (modes_zero stress index) (modes_closed stress index) value
  change ‖NativeFiniteActionResolvent.coefficients (modes stress index) input‖ ≤ ‖value‖ at loadPaid
  change ‖NativeFiniteActionResolvent.coefficients (modes stress index) input‖ ^ 2 =
    ‖NativeFiniteActionResolvent.coefficients (modes stress index) solved‖ ^ 2 +
    ‖NativeFiniteActionResolvent.coefficients (modes stress index) (input - solved)‖ ^ 2 +
    2 * step * nu.coeff * curlPair (modes stress index) solved.1 solved.1 at balance
  nlinarith [sq_nonneg ‖NativeFiniteActionResolvent.coefficients (modes stress index) solved‖,
    sq_nonneg ‖NativeFiniteActionResolvent.coefficients (modes stress index) (input - solved)‖,
    norm_nonneg (NativeFiniteActionResolvent.coefficients (modes stress index) input)]

theorem source_pointwise (stress : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (value : wholePhysical) :
    ∃ target : State, Tendsto (fun index => stageOperator stress pointLe index node step positive.le value)
      ((generated stress pointLe).refinement : Filter ℕ) (𝓝 target) ∧
      Summable (curlDensity target) ∧ (∑' wave, curlDensity target wave) ≤ ‖value‖ ^ 2 / (2 * step * nu.coeff) :=
  exists_strong_limit_of_sum (fun index => stageOperator stress pointLe index node step positive.le value)
    (generated stress pointLe).refinement _
    (fun index => (stage_curl_budget stress pointLe index node step positive value).1)
    (fun index => (stage_curl_budget stress pointLe index node step positive value).2)

theorem stage_physical (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ) (node : TimeNode)
    (step : ℝ) (nonnegative : 0 ≤ step) (value : wholePhysical) :
    stageOperator stress pointLe index node step nonnegative value ∈ wholePhysical := by
  let solved := physicalResolver (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index node) (advector_reality stress pointLe index node) step nonnegative
    (restrictCLM (modes stress index) (modes_zero stress index) (modes_closed stress index) value)
  change WholeRestartVelocityEndpointTransverse (puncturedEuclideanize solved.1) ∧
    WholeRestartVelocityEndpointReality (puncturedEuclideanize solved.1)
  constructor
  · intro wave
    exact finiteTransverseSupportProjection_fixed_transverse solved.2.1 wave.1
  · intro wave coordinate
    exact congrFun (physical_reality (fun {_} member => modes_closed stress index _ member) solved wave.1) coordinate

end
end SaturationMonoid.NavierStokes.NativeWholeResolvent
