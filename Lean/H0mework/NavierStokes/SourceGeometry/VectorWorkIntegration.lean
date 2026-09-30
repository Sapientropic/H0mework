import H0mework.NavierStokes.Energy.ClosedEnstrophyPhysicalBridge
import H0mework.NavierStokes.Fourier.FullVorticityDifferentialTransport

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicLocalEnergyFluxTransport
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalPeriodicFullVorticityDifferentialTransport
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore

noncomputable section

theorem velocityDot_eq_inner (u v : PhysicalSpace → PhysicalSpace) (x : PhysicalSpace) :
    velocityDot u v x = inner ℝ (u x) (v x) := by
  simp only [velocityDot, PiLp.inner_apply, Real.inner_apply]

private theorem linear_apply_sum (D : PhysicalSpace →L[ℝ] ℝ) (v : PhysicalSpace) :
    D v = ∑ i : Coordinate, v i * D (EuclideanSpace.single i 1) := by
  rw [← (EuclideanSpace.basisFun Coordinate ℝ).sum_repr v, map_sum]
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    map_smul, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, PiLp.single_apply, mul_ite, mul_one,
    mul_zero, Fintype.sum_ite_eq]

theorem physicalUnitCell_mixed_transport_integral
    (a b c : PhysicalSpace → PhysicalSpace)
    (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) (hc : ContDiff ℝ 1 c)
    (pa : LatticePeriodic a) (pb : LatticePeriodic b) (pc : LatticePeriodic c)
    (divc : velocityDivergence c = 0) :
    (∫ x in physicalUnitCell, inner ℝ (a x) (fderiv ℝ b x (c x))) =
      -(∫ x in physicalUnitCell, inner ℝ (b x) (fderiv ℝ a x (c x))) := by
  let p : PhysicalSpace → ℝ := fun x => inner ℝ (a x) (b x)
  have hp : ContDiff ℝ 1 p := ha.inner ℝ hb
  have pp : LatticePeriodic p := by
    intro z x
    simp only [p, pa z x, pb z x]
  have fluxZero := physicalUnitCell_velocityDivergence_integral_eq_zero
    (pressureEnergyFlux p c) (pressureEnergyFlux_contDiff p c hp hc)
    (pressureEnergyFlux_latticePeriodic p c pp pc)
  have identity (x : PhysicalSpace) :
      velocityDivergence (pressureEnergyFlux p c) x =
        inner ℝ (a x) (fderiv ℝ b x (c x)) +
          inner ℝ (b x) (fderiv ℝ a x (c x)) := by
    have h := congrFun (velocityDot_scalarGradient p c
      (hp.differentiable (by norm_num)) (hc.differentiable (by norm_num))) x
    simp only [Pi.sub_apply, divc, Pi.zero_apply, mul_zero, sub_zero] at h
    rw [← h]
    change (∑ i : Coordinate, c x i *
      fderiv ℝ p x (EuclideanSpace.single i 1)) = _
    rw [← linear_apply_sum]
    dsimp only [p]
    rw [fderiv_inner_apply ℝ (ha.differentiable (by norm_num) x)
      (hb.differentiable (by norm_num) x) (c x)]
    rw [real_inner_comm (fderiv ℝ a x (c x)) (b x), add_comm]
  have ca : Continuous (fun x => fderiv ℝ a x (c x)) :=
    (ha.continuous_fderiv (by norm_num)).clm_apply hc.continuous
  have cb : Continuous (fun x => fderiv ℝ b x (c x)) :=
    (hb.continuous_fderiv (by norm_num)).clm_apply hc.continuous
  have ia : IntegrableOn (fun x => inner ℝ (b x) (fderiv ℝ a x (c x)))
      physicalUnitCell := (hb.continuous.inner ca).continuousOn.integrableOn_compact
        physicalUnitCell_isCompact
  have ib : IntegrableOn (fun x => inner ℝ (a x) (fderiv ℝ b x (c x)))
      physicalUnitCell := (ha.continuous.inner cb).continuousOn.integrableOn_compact
        physicalUnitCell_isCompact
  simp_rw [identity] at fluxZero
  rw [integral_add ib ia] at fluxZero
  linarith

theorem physicalUnitCell_source_work_integral (source : RawVorticityFourierSource) :
    (∫ x in physicalUnitCell, enstrophyStretchingWork (physicalVelocity source) x) =
      -(∫ x in physicalUnitCell, inner ℝ (physicalVelocity source x)
        (fderiv ℝ (physicalVorticity source) x (physicalVorticity source x))) := by
  have hdiv : velocityDivergence (physicalVorticity source) = 0 := by
    rw [← vorticityField_physicalVelocity]
    exact velocityDivergence_vorticityField_eq_zero _
      ((physicalVelocity_contDiff source).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have h := physicalUnitCell_mixed_transport_integral
    (physicalVorticity source) (physicalVelocity source) (physicalVorticity source)
    ((physicalVorticity_contDiff source).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    ((physicalVelocity_contDiff source).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    ((physicalVorticity_contDiff source).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    (physicalVorticity_latticePeriodic source) (physicalVelocity_latticePeriodic source)
    (physicalVorticity_latticePeriodic source) hdiv
  simpa only [enstrophyStretchingWork, vortexStretching,
    vorticityField_physicalVelocity, velocityDot_eq_inner] using h

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
