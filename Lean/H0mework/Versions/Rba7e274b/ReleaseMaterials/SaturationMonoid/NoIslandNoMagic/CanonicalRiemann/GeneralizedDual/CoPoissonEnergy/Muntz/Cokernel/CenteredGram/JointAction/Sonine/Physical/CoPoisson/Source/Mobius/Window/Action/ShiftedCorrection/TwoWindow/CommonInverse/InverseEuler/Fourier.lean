import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex Filter FourierTransform MeasureTheory Set OriginalRieszSource
open scoped ENNReal InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
attribute [local instance 1100] NormedSpace.complexToReal
local notation "μband" h => volume.restrict (sourceBand h)

def bandFourier (h : ℝ) (raw : ℝ→ℂ) (frequency : ℝ) : ℂ :=
  VectorFourier.fourierIntegral 𝐞 (μband h) (innerₗ ℝ) raw frequency
def bandDerivative (h : ℝ) (raw : ℝ→ℂ) (frequency : ℝ) : ℂ :=
  (VectorFourier.fourierIntegral 𝐞 (μband h) (innerSL ℝ).toLinearMap₁₂
    (VectorFourier.fourierSMulRight (innerSL ℝ) raw) frequency) 1

private theorem band_integrable (h : ℝ) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) : Integrable raw (μband h) :=
  continuous.integrableOn_Icc
private theorem band_moment_integrable (h : ℝ) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) :
    Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) raw) (μband h) := by
  apply (show ContinuousOn (VectorFourier.fourierSMulRight (innerSL ℝ) raw)
    (sourceBand h) from ?_).integrableOn_Icc
  unfold VectorFourier.fourierSMulRight
  have paired : ContinuousOn (fun x:ℝ=>((innerSL ℝ) x,raw x)) (sourceBand h) :=
    (innerSL ℝ).continuous.continuousOn.prodMk continuous
  exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ).continuous₂.comp_continuousOn
    paired).const_smul (-(2*(Real.pi:ℂ)*Complex.I):ℂ)

theorem bandFourier_hasDerivAt (h : ℝ) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) (frequency : ℝ) :
    HasDerivAt (bandFourier h raw) (bandDerivative h raw frequency) frequency := by
  have moment : Integrable (fun x:ℝ=>‖x‖*‖raw x‖) (μband h) :=
    (show ContinuousOn (fun x:ℝ=>‖x‖*‖raw x‖) (sourceBand h) from by
      fun_prop).integrableOn_Icc
  have generated:=VectorFourier.hasFDerivAt_fourierIntegral (innerSL ℝ)
    (band_integrable h raw continuous) moment frequency
  unfold bandFourier bandDerivative
  have bilinear : (innerₗ ℝ)=(innerSL ℝ).toLinearMap₁₂ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [innerₗ_apply_apply,ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      innerSL_apply_apply]
  rw [bilinear]
  exact generated.hasDerivAt

theorem bandFourier_continuous (h : ℝ) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) : Continuous (bandFourier h raw) :=
  continuous_iff_continuousAt.mpr fun x=>(bandFourier_hasDerivAt h raw continuous x).continuousAt
theorem bandDerivative_continuous (h : ℝ) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) : Continuous (bandDerivative h raw) := by
  unfold bandDerivative
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,innerSL_apply_apply]
      using (continuous_inner : Continuous (fun p:ℝ×ℝ=>inner ℝ p.1 p.2)))
    (band_moment_integrable h raw continuous)).clm_apply continuous_const

def cotestMean (scale : ℝ) (field : BurnolL2) : ℂ :=
  burnolQuarterMeanCoefficient (burnolQuarterRestriction
    (burnolAmbientEvenPart (fourierL2 (burnolMultiplicativeDilation (-scale) field))))
def evenBandFourier (h scale : ℝ) (raw : ℝ→ℂ) (x : ℝ) : ℂ :=
  (Real.exp (scale/2):ℂ)/2 *
    (bandFourier h raw (Real.exp scale*x)+bandFourier h raw (-(Real.exp scale*x)))
def evenBandDerivative (h scale : ℝ) (raw : ℝ→ℂ) (x : ℝ) : ℂ :=
  (Real.exp (scale/2):ℂ)/2*(Real.exp scale:ℂ)*
    (bandDerivative h raw (Real.exp scale*x)-bandDerivative h raw (-(Real.exp scale*x)))

theorem evenBandFourier_hasDerivAt (h scale : ℝ) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) (x : ℝ) :
    HasDerivAt (evenBandFourier h scale raw) (evenBandDerivative h scale raw x) x := by
  have plus:=(bandFourier_hasDerivAt h raw continuous (Real.exp scale*x)).scomp x
    ((hasDerivAt_id x).const_mul (Real.exp scale))
  have minus:=(bandFourier_hasDerivAt h raw continuous (-(Real.exp scale*x))).scomp x
    (((hasDerivAt_id x).const_mul (Real.exp scale)).neg)
  have source : HasDerivAt (evenBandFourier h scale raw)
      ((Real.exp (scale/2):ℂ)/2*((Real.exp scale:ℂ)*bandDerivative h raw (Real.exp scale*x)+
        (-(Real.exp scale:ℂ))*bandDerivative h raw (-(Real.exp scale*x)))) x := by
    simpa only [evenBandFourier,Function.comp_def,Pi.add_apply,Pi.mul_apply,id_eq,mul_one,
      Pi.neg_apply,real_smul,Complex.ofReal_neg] using!
      (plus.add minus).const_mul ((Real.exp (scale/2):ℂ)/2)
  convert! source using 1
  unfold evenBandDerivative
  ring

def bCotestRaw (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) (x : ℝ) : ℂ :=
  evenBandFourier h scale (bLeg coordinate leg) x-cotestMean scale (bBand coordinate h leg)
def pCotestRaw (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) (x : ℝ) : ℂ :=
  evenBandFourier h scale (pLeg coordinate leg) x-cotestMean scale (pBand coordinate h leg)

theorem bCotestRaw_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg x : ℝ) :
    HasDerivAt (bCotestRaw coordinate h scale leg)
      (evenBandDerivative h scale (bLeg coordinate leg) x) x :=
  (evenBandFourier_hasDerivAt h scale (bLeg coordinate leg)
    (bLeg_continuousOn coordinate h leg) x).sub_const _
theorem pCotestRaw_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg x : ℝ) :
    HasDerivAt (pCotestRaw coordinate h scale leg)
      (evenBandDerivative h scale (pLeg coordinate leg) x) x :=
  (evenBandFourier_hasDerivAt h scale (pLeg coordinate leg)
    (pLeg_continuousOn coordinate h leg) x).sub_const _
theorem bCotestRaw_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) : Continuous (bCotestRaw coordinate h scale leg) :=
  continuous_iff_continuousAt.mpr fun x=>(bCotestRaw_hasDerivAt coordinate h scale leg x).continuousAt
theorem pCotestRaw_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) : Continuous (pCotestRaw coordinate h scale leg) :=
  continuous_iff_continuousAt.mpr fun x=>(pCotestRaw_hasDerivAt coordinate h scale leg x).continuousAt

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
