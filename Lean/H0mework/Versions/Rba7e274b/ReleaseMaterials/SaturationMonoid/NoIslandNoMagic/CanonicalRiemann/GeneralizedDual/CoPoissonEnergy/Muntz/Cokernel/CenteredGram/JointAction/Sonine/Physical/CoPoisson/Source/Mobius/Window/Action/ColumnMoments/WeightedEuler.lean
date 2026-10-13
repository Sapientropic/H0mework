import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.DivisorPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped Topology InnerProductSpace
open OriginalRieszSource

def weightedEndpointResponse (coordinate : BurnolCompletedMellinCoordinate) (lower : ℝ) : ℂ :=
  ((1/4:ℂ)^(1-star coordinate.value))*Kernel.beta coordinate-
    (lower:ℂ)^(1-star coordinate.value)*burnolRieszSingleFourierSourceRaw coordinate lower-
    Kernel.beta coordinate*(∫ y : ℝ in lower..(1/4:ℝ),(y:ℂ)^(-star coordinate.value))

-- The actual Rplus-star weight cancels the b source Euler coefficient, including the beta boundary.
theorem weighted_source_derivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    HasDerivAt (fun y : ℝ=>(y:ℂ)^(1-star coordinate.value)*burnolRieszSingleFourierSourceRaw coordinate y)
      ((x:ℂ)^(-star coordinate.value)*(OriginalRieszSourceGreen.weightedRaw coordinate x-
        (star coordinate.value-1/2)*burnolRieszSingleFourierSourceRaw coordinate x)) x := by
  have slit : (x:ℂ)∈Complex.slitPlane := by simp only [Complex.mem_slitPlane_iff,Complex.ofReal_re,Complex.ofReal_im];exact Or.inl positive
  have power := (Complex.hasStrictDerivAt_cpow_const slit (c:=1-star coordinate.value)).hasDerivAt.comp_ofReal
  have generated := power.mul (OriginalRieszSourceGreen.sourceRaw_hasDerivAt coordinate x positive.ne')
  convert! generated using 1
  have powerScale : (x:ℂ)^(1-star coordinate.value)=(x:ℂ)^(-star coordinate.value)*(x:ℂ) := by
    rw [show 1-star coordinate.value=-star coordinate.value+1 by ring,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),Complex.cpow_one]
  rw [powerScale,show 1-star coordinate.value-1=-star coordinate.value by ring]
  have source := OriginalRieszSourceGreen.sourceRaw_weighted_eq coordinate x positive.ne'
  linear_combination -((x:ℂ)^(-star coordinate.value))*source

theorem original_response_weighted_band (coordinate : BurnolCompletedMellinCoordinate) (lower : ℝ)
    (positive : 0<lower) (bounded : lower≤(1/4:ℝ)) :
    (∫ y : ℝ in lower..(1/4:ℝ),(y:ℂ)^(-star coordinate.value)*contactResponse coordinate y)=
      weightedEndpointResponse coordinate lower := by
  have powerContinuous : ContinuousOn (fun x : ℝ=>(x:ℂ)^(-star coordinate.value)) (Icc lower (1/4:ℝ)) := by
    intro x inside
    apply ContinuousAt.continuousWithinAt
    have slit : (x:ℂ)∈Complex.slitPlane := by
      simp only [Complex.mem_slitPlane_iff,Complex.ofReal_re,Complex.ofReal_im]
      exact Or.inl (positive.trans_le inside.1)
    exact ((Complex.hasStrictDerivAt_cpow_const slit (c:=-star coordinate.value)).hasDerivAt.comp_ofReal).continuousAt
  have rawContinuous : ContinuousOn (burnolRieszSingleFourierSourceRaw coordinate) (Icc lower (1/4:ℝ)) :=
    fun x inside=>(burnolRieszSingleFourierSourceRaw_continuousAt coordinate (positive.trans_le inside.1).ne').continuousWithinAt
  have weightedContinuous : ContinuousOn (OriginalRieszSourceGreen.weightedRaw coordinate) (Icc lower (1/4:ℝ)) :=
    fun x inside=>(source_weighted_continuous coordinate (positive.trans_le inside.1).ne').continuousWithinAt
  have sourceDerivative (x : ℝ) (inside : x∈uIcc lower (1/4:ℝ)) :=
    weighted_source_derivative coordinate x (positive.trans_le (show x∈Icc lower (1/4:ℝ) by simpa only [uIcc_of_le bounded] using inside).1)
  have integrated := intervalIntegral.integral_eq_sub_of_hasDerivAt sourceDerivative
    ((powerContinuous.mul (weightedContinuous.sub (continuousOn_const.mul rawContinuous))).intervalIntegrable_of_Icc bounded)
  have source : (∫ y : ℝ in lower..(1/4:ℝ),(y:ℂ)^(-star coordinate.value)*contactResponse coordinate y)=
      (∫ y : ℝ in lower..(1/4:ℝ),(y:ℂ)^(-star coordinate.value)*(OriginalRieszSourceGreen.weightedRaw coordinate y-
        (star coordinate.value-1/2)*burnolRieszSingleFourierSourceRaw coordinate y))-
      Kernel.beta coordinate*(∫ y : ℝ in lower..(1/4:ℝ),(y:ℂ)^(-star coordinate.value)) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr_ae_restrict
      have read := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp (original_contact_response_read coordinate)
      filter_upwards [ae_restrict_of_ae read,ae_restrict_mem measurableSet_uIoc] with y actual inside
      have band : y∈Ioc lower (1/4:ℝ) := by simpa only [uIoc_of_le bounded] using inside
      rw [actual ⟨by linarith [band.1],band.2⟩]
      ring
    · exact (powerContinuous.mul (weightedContinuous.sub (continuousOn_const.mul rawContinuous))).intervalIntegrable_of_Icc bounded
    · exact (continuousOn_const.mul powerContinuous).intervalIntegrable_of_Icc bounded
  rw [source,integrated]
  unfold weightedEndpointResponse Kernel.beta
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
