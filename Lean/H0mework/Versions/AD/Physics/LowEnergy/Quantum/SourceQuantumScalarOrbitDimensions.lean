import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceQuantumNativeDimensions
import H0mework.Physics.Admission.ResidualLimitScalarBalanceClosure

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
noncomputable section
namespace LowEnergy.SourceQuantumScalarOrbitDimensions
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorYukawaMassSpectrum
open StageNineCoframeScalarMatterRegularity StageNineExteriorMotherLieRepresentation
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open scoped RealInnerProductSpace

private def brokenCoordinates : (Fin 9 → ℝ) →ₗ[ℝ] ((Fin 8 → ℝ) × (Fin 3 → ℝ) × ℝ) where
  toFun x := (![0,0,x 0,x 1,x 2,x 3,0,x 4], ![x 5,x 6,x 7], x 8)
  map_add' := by
    intro x y
    apply Prod.ext
    · ext i; fin_cases i <;> simp
    · apply Prod.ext
      · ext i; fin_cases i <;> simp
      · rfl
  map_smul' := by
    intro r x
    apply Prod.ext
    · ext i; fin_cases i <;> simp
    · apply Prod.ext
      · ext i; fin_cases i <;> simp
      · simp

private def brokenBuild : (Fin 9 → ℝ) →ₗ[ℝ] NativeLie :=
  nativeCoordinates.symm.toLinearMap.comp brokenCoordinates

private def orbitRead : Scalar →ₗ[ℝ] (Fin 9 → ℝ) where
  toFun x := ![(x (sourceOrbitReadIndex 2)).re, -(x (sourceOrbitReadIndex 2)).im,
    -(x (sourceOrbitReadIndex 1)).re, (x (sourceOrbitReadIndex 1)).im,
    (x (sourceOrbitReadIndex 5)).im - (x (sourceOrbitReadIndex 3)).im + (x (sourceOrbitReadIndex 4)).im,
    (x (sourceOrbitReadIndex 0)).re, (x (sourceOrbitReadIndex 0)).im,
    -(x (sourceOrbitReadIndex 3)).im, -(x (sourceOrbitReadIndex 4)).im]
  map_add' := by
    intros
    ext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' := by intros; ext i; fin_cases i <;> simp [mul_add, mul_sub]

private theorem orbitRead_build (x : Fin 9 → ℝ) : orbitRead (orbit (brokenBuild x)) = x := by
  ext i
  fin_cases i <;> simp [orbitRead, brokenBuild, brokenCoordinates, sourceOrbit_read]
  ring

private theorem orbit_rank_lower : 9 ≤ Module.finrank ℝ orbit.range := by
  let f := orbit.rangeRestrict.comp brokenBuild
  have hi : Function.Injective f := by
    intro x y h
    have h' := congrArg (fun z : orbit.range => orbitRead z) h
    change orbitRead (orbit (brokenBuild x)) = orbitRead (orbit (brokenBuild y)) at h'
    simpa only [orbitRead_build] using h'
  simpa using LinearMap.finrank_le_finrank_of_injective hi

open SU7MotherGaugeTheory StageNineResidualLimitScalarBalanceClosure

private def kernelBlock : Fin 3 → P286LieBlockData :=
  ![(colorMixingGenerator,0,0), (colorCartanGenerator,0,0),
    p286LieBracket (colorCartanGenerator,0,0) (colorMixingGenerator,0,0)]

private def kernelVector (i : Fin 3) : NativeLie := p286CoordinateEquiv (kernelBlock i)

private theorem orbit_block (a : P286LieBlockData) :
    orbit (p286CoordinateEquiv a) = scalarCoordinateEquiv
      (exteriorMotherLieAction 4 (p286LieBlockEmbed a) finiteGenerationJointBreakingScalar) := by
  change scalarMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv a)))
    (sourceGeneratedVacuumCoordinates StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource) = _
  rw [p286CoordinateEquiv.symm_apply_apply]
  unfold scalarMotherLieAction sourceGeneratedVacuumCoordinates
  rw [scalarCoordinateEquiv.symm_apply_apply, positive_sourceGeneratedVacuumBase]

private theorem kernelVector_zero (i : Fin 3) : orbit (kernelVector i) = 0 := by
  unfold kernelVector
  rw [orbit_block]
  fin_cases i
  · simpa [kernelBlock, colorMixingMotherDirection] using congrArg scalarCoordinateEquiv
      finiteGenerationJointBreakingScalar_colorMixing_action_zero
  · simpa [kernelBlock, colorCartanMotherDirection] using congrArg scalarCoordinateEquiv
      finiteGenerationJointBreakingScalar_colorCartan_action_zero
  · change scalarCoordinateEquiv (exteriorMotherLieAction 4
      (p286LieBlockEmbed (p286LieBracket (colorCartanGenerator,0,0) (colorMixingGenerator,0,0)))
        finiteGenerationJointBreakingScalar) = 0
    rw [p286LieBlockEmbed_bracket, exteriorMotherLieAction_bracket]
    change scalarCoordinateEquiv
      (exteriorMotherLieAction 4 colorCartanMotherDirection
        (exteriorMotherLieAction 4 colorMixingMotherDirection finiteGenerationJointBreakingScalar) -
       exteriorMotherLieAction 4 colorMixingMotherDirection
        (exteriorMotherLieAction 4 colorCartanMotherDirection finiteGenerationJointBreakingScalar)) = 0
    rw [finiteGenerationJointBreakingScalar_colorMixing_action_zero,
      finiteGenerationJointBreakingScalar_colorCartan_action_zero]
    simp

private theorem kernelVector_coordinates (i : Fin 3) : nativeCoordinates (kernelVector i) =
    ![(![1,0,0,0,0,0,0,0],0,0),(![0,0,0,0,0,0,1,0],0,0),
      (![0,2,0,0,0,0,0,0],0,0)] i := by
  simp only [kernelVector, nativeCoordinates_apply]
  fin_cases i <;> ext j
  all_goals try fin_cases j
  all_goals
    norm_num [kernelBlock, p286LieBracket, suLieBracket,
      colorCartanGenerator, colorCartanRaw, colorMixingGenerator, colorMixingRaw,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := Ne.symm h20
    have h12 : (1 : Fin 3) ≠ 2 := Ne.symm h21
    simp_all

private def kernelBuild : (Fin 3 → ℝ) →ₗ[ℝ] NativeLie where
  toFun x := ∑ i : Fin 3, x i • kernelVector i
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum, smul_smul]

private theorem kernelBuild_coordinates (x : Fin 3 → ℝ) :
    nativeCoordinates (kernelBuild x) = (![x 0,2*x 2,0,0,0,0,x 1,0],0,0) := by
  change nativeCoordinates (∑ i : Fin 3, x i • kernelVector i) = _
  rw [map_sum]
  simp_rw [map_smul, kernelVector_coordinates]
  simp [Fin.sum_univ_three, mul_comm]

private theorem kernelBuild_injective : Function.Injective kernelBuild := by
  intro x y h
  have hr := congrArg nativeCoordinates h
  rw [kernelBuild_coordinates, kernelBuild_coordinates] at hr
  have h0 := congrArg (fun z : (Fin 8 → ℝ) × (Fin 3 → ℝ) × ℝ => z.1 0) hr
  have h1 := congrArg (fun z : (Fin 8 → ℝ) × (Fin 3 → ℝ) × ℝ => z.1 6) hr
  have h2 := congrArg (fun z : (Fin 8 → ℝ) × (Fin 3 → ℝ) × ℝ => z.1 1) hr
  simp at h0 h1 h2
  ext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem kernelBuild_mem (x : Fin 3 → ℝ) : kernelBuild x ∈ stabilizer := by
  change orbit (∑ i : Fin 3, x i • kernelVector i) = 0
  simp [kernelVector_zero]

private theorem stabilizer_rank_lower : 3 ≤ Module.finrank ℝ stabilizer := by
  let f := kernelBuild.codRestrict stabilizer kernelBuild_mem
  have hi : Function.Injective f := by
    intro x y h
    exact kernelBuild_injective (congrArg Subtype.val h)
  simpa using LinearMap.finrank_le_finrank_of_injective hi

theorem orbit_finrank : Module.finrank ℝ orbit.range = 9 := by
  have hr := orbit.finrank_range_add_finrank_ker
  rw [nativeLie_finrank] at hr
  have hk := stabilizer_rank_lower
  have hl := orbit_rank_lower
  change 3 ≤ Module.finrank ℝ orbit.ker at hk
  omega

theorem stabilizer_finrank : Module.finrank ℝ stabilizer = 3 := by
  have hr := orbit.finrank_range_add_finrank_ker
  rw [nativeLie_finrank, orbit_finrank] at hr
  change Module.finrank ℝ orbit.ker = 3
  omega

theorem broken_finrank : Module.finrank ℝ broken = 9 := by
  have h := stabilizer.finrank_add_finrank_orthogonal
  rw [stabilizer_finrank, nativeLie_finrank] at h
  change Module.finrank ℝ stabilizerᗮ = 9
  omega

theorem scalarSlice_finrank : Module.finrank ℝ scalarSlice = 61 := by
  have h := orbit.range.finrank_add_finrank_orthogonal
  rw [orbit_finrank, scalar_finrank] at h
  change Module.finrank ℝ orbit.rangeᗮ = 61
  omega

theorem configuration_finrank : Module.finrank ℝ SourceQuantumConfigurationHilbert.Configuration = 103 := by
  rw [SourceQuantumConfigurationHilbert.configuration_finrank, scalarSlice_finrank, nativeLie_finrank]

end LowEnergy.SourceQuantumScalarOrbitDimensions
