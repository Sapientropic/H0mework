import H0mework.NavierStokes.EvenLattice.Finite
import H0mework.NavierStokes.ReferenceErrorCritical.Approximation
import H0mework.NavierStokes.SourceGeometry.SymmetryFields

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set Filter
open scoped Topology
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin

noncomputable section

theorem whole_even_work_sq_le (field : ComplexVorticityHilbertState)
    (zeroRow : field 0 = 0) (transverse : WholeStateTransverse field)
    (reality : FiniteStateFourierReality field) (even : SourceEvenFrequency.OnEvenLattice field)
    (gradient : Summable fun k => integerWaveNormSq k * complexCoordinateAmplitudeSq (field k)) :
    NonlinearWork.value field ^ 2 ≤ (63 / 8) * wholeVorticityEuclideanMass field *
      wholeStateVorticityGradientMass field ^ 2 := by
  apply le_of_tendsto (CriticalError.projected_work_tendsto field zeroRow transverse gradient |>.pow 2)
  apply Filter.Eventually.of_forall
  intro radius
  let base := puncturedIntegerWaveFrequencyCube radius
  let modes := base.filter (fun k => Even (k 0))
  let projected := complexSharpSupportProjection modes field
  have zeroNotMem : 0 ∉ modes := by simp [modes, base, puncturedIntegerWaveFrequencyCube]
  have negClosed : ∀ k ∈ modes, waveNeg k ∈ modes := by
    intro k hk
    obtain ⟨member, parity⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member,
      by simpa only [waveNeg, Pi.neg_apply] using parity.neg⟩
  have parity : ∀ k ∈ modes, 2 ∣ k 0 := fun k hk => (Finset.mem_filter.mp hk).2.two_dvd
  have supported := complexSharpSupportProjection_supported modes field
  have physical := wholeStateTransverse_sharpSupportProjection modes field transverse
  have realField := complexSharpSupportProjection_reality modes field negClosed reality
  have same : complexSharpSupportProjection base field = projected := by
    apply lp.ext
    funext k
    by_cases hk : k ∈ base
    · by_cases he : Even (k 0)
      · simp [projected, modes, complexSharpSupportProjection_apply, hk, he]
      · simp [projected, modes, complexSharpSupportProjection_apply, hk, he, even k he]
    · simp [projected, modes, complexSharpSupportProjection_apply, hk]
  have work : NonlinearWork.value projected = finiteStateVorticityStretchingWork modes projected := by
    calc
      _ = NonlinearWork.value (complexSharpSupportProjection modes projected) :=
        congrArg NonlinearWork.value (complexSharpSupportProjection_eq_self_of_supported modes projected supported).symm
      _ = finiteStateVorticityNonlinearWork modes projected := CriticalError.projected_work_eq_finite modes projected
      _ = _ := finiteStateVorticityNonlinearWork_eq_stretchingWork modes negClosed projected realField
  have bound := finite_even_work_sq_le modes zeroNotMem negClosed parity projected supported
    (fun k _ => physical k) realField
  have mass : finiteStateVorticityCoefficientEnstrophy modes projected ≤ wholeVorticityEuclideanMass field := by
    dsimp only [projected]
    rw [finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
    exact finiteStateVorticityCoefficientEnstrophy_le_wholeMass modes field
  have gradientSame : finiteStateVorticityEnstrophyMass modes projected = finiteStateVorticityEnstrophyMass modes field := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [projected, complexSharpSupportProjection_apply, hk]
  have gradientLe := gradientSame.le.trans (finiteStateVorticityEnstrophyMass_le_wholeGradientMass modes field gradient)
  have massNonneg : 0 ≤ wholeVorticityEuclideanMass field := tsum_nonneg fun _ => sq_nonneg _
  have squared := (sq_le_sq₀ (finiteStateVorticityEnstrophyMass_nonneg modes projected)
    ((finiteStateVorticityEnstrophyMass_nonneg modes projected).trans gradientLe)).2 gradientLe
  have paid := mul_le_mul (mul_le_mul_of_nonneg_left mass (by norm_num : (0 : Real) ≤ 63 / 8)) squared
    (sq_nonneg _) (by positivity : (0 : Real) ≤ 63 / 8 * wholeVorticityEuclideanMass field)
  change NonlinearWork.value (complexSharpSupportProjection base field) ^ 2 ≤ _
  rw [same, work]
  exact bound.trans paid

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
