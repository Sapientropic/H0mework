import H0mework.NavierStokes.SourceAction.HilbertDiracCurrent

set_option autoImplicit false
open scoped BigOperators ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeResolvedPairingTransfer

open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeStressPairingCarrier NativeHilbertDiracCurrent NativeEndpointVelocityCarrier NativePhysicalFourier
open NativeCofinalStressPositivity (Index)

noncomputable section

def resolved (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean) : Data where
  mean := mean
  reality := reality
  stress := NativeStressSource.quadraticFlux (wholeVelocity mean)
  positive := by
    constructor
    · ext left right
      simp [covariance]
    · intro coefficients
      simp [covariance]

instance resolved_residual_subsingleton (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean) :
    Subsingleton (NativePositiveKernelCarrier.Space (kernel (resolved mean reality))) := by
  have allZero (value : NativePositiveKernelCarrier.Space (kernel (resolved mean reality))) : value = 0 := by
    induction value using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq continuous_id continuous_const
    | ih value =>
        apply norm_eq_zero.mp
        rw [UniformSpace.Completion.norm_coe]
        apply sq_eq_zero_iff.mp
        rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
        change (NativePositiveKernelCarrier.pairing (kernel (resolved mean reality)) value value).re = 0
        simp [NativePositiveKernelCarrier.pairing, kernel, covariance, resolved]
  exact ⟨fun first second => (allZero first).trans (allZero second).symm⟩

def transfer (destination : Data) (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean) :
    Space (resolved mean reality) →ₗᵢ[ℂ] Space destination where
  toFun value := WithLp.toLp 2 (WithLp.fst value, 0)
  map_add' first second := by
    apply WithLp.ofLp_injective
    simp
  map_smul' scalar value := by
    apply WithLp.ofLp_injective
    simp
  norm_map' value := by
    change ‖(WithLp.toLp 2 (WithLp.fst value, (0 : NativePositiveKernelCarrier.Space (kernel destination))) : Space destination)‖ = ‖value‖
    rw [WithLp.norm_toLp_fst]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    have zero : WithLp.snd value = 0 := Subsingleton.elim _ _
    rw [zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

def mapSpinor {first second : Data} (linear : Space first →ₗ[ℂ] Space second) (vector : Spinor first) : Spinor second :=
  fun spin color => linear (vector spin color)

theorem action_map {first second : Data} (linear : Space first →ₗ[ℂ] Space second) (matrix : DiracMatrix) (vector : Spinor first) :
    action second matrix (mapSpinor linear vector) = mapSpinor linear (action first matrix vector) := by
  funext spin color
  simp only [action, mapSpinor, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]

theorem canonicalDual_map {first second : Data} (isometry : Space first →ₗᵢ[ℂ] Space second) (left right : Spinor first) :
    canonicalDual second (mapSpinor isometry.toLinearMap left) (mapSpinor isometry.toLinearMap right) = canonicalDual first left right := by
  change (∑ spin : Fin 4, ∑ color : Fin 2,
    inner ℂ (action second diracAdjointSpinSwap (mapSpinor isometry.toLinearMap left) spin color)
      (mapSpinor isometry.toLinearMap right spin color)) = _
  rw [action_map]
  simp only [mapSpinor, LinearIsometry.coe_toLinearMap, LinearIsometry.inner_map_map]
  rfl

def writtenMatter (destination : Data) (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean)
    (wave : IntegerWavevector) : Spinor destination :=
  mapSpinor (transfer destination mean reality).toLinearMap (matter (resolved mean reality) wave)

def writtenCurrent (destination : Data) (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean)
    (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  canonicalDual destination (writtenMatter destination mean reality wave)
    (action destination (diracGamma direction) (writtenMatter destination mean reality 0))

theorem writtenCurrent_eq (destination : Data) (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean)
    (direction : Fin 4) (wave : IntegerWavevector) :
    writtenCurrent destination mean reality direction wave = NativePairedCurrentFourier.coefficient (wholeVelocity mean)
      (NativeStressSource.quadraticFlux (wholeVelocity mean)) direction wave := by
  unfold writtenCurrent writtenMatter
  rw [action_map, canonicalDual_map]
  change diracCurrent (resolved mean reality) direction wave = _
  rw [diracCurrent_eq (resolved mean reality) direction wave (NativeStressSource.quadraticFlux_symmetric _ wave), pairedCurrent_eq]
  rfl

end
end SaturationMonoid.NavierStokes.NativeResolvedPairingTransfer
