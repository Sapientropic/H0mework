import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.Wave

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
namespace NativeWeight
export OriginalRieszFinitePairing.CoPoisson
  (bandLower bandLower_pos bandLower_le_four positionWeight fourierWeight
   positionWeight_hasDerivAt fourierWeight_hasDerivAt
   positionWeight_deriv_continuousOn fourierWeight_deriv_continuousOn)
end NativeWeight

private def primitiveStep (primitive : ℝ → BurnolL2) (lower upper : ℝ)
    (weight slope : ℝ → ℂ) : BurnolL2 :=
  weight upper • (primitive upper-primitive lower)-
    ∫ u : ℝ in Ioc lower upper, slope u • (primitive u-primitive lower)

private theorem primitive_stock (primitive : ℝ → BurnolL2)
    (continuous : ContinuousOn primitive (Ioi 0)) (lower upper : ℝ)
    (positive : 0<lower) (ordered : lower≤upper) (weight slope : ℝ → ℂ)
    (derivative : ∀ u∈Icc lower upper, HasDerivAt weight (slope u) u)
    (regular : ContinuousOn slope (Icc lower upper)) :
    primitiveStep primitive lower upper weight slope=
      weight upper • primitive upper-weight lower • primitive lower-
        ∫ u : ℝ in Ioc lower upper, slope u • primitive u := by
  have primitiveContinuous:ContinuousOn primitive (Icc lower upper):=
    continuous.mono (fun _ inside=>positive.trans_le inside.1)
  have first:IntegrableOn (fun u=>slope u • primitive u) (Ioc lower upper):=
    (regular.smul primitiveContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have second:IntegrableOn (fun u=>slope u • primitive lower) (Ioc lower upper):=
    (regular.smul continuousOn_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have slopeRead:(∫ u : ℝ in Ioc lower upper, slope u)=weight upper-weight lower := by
    rw [← intervalIntegral.integral_of_le ordered]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u inside=>derivative u (by simpa only [uIcc_of_le ordered] using inside))
      (regular.intervalIntegrable_of_Icc ordered)
  unfold primitiveStep
  simp_rw [smul_sub]
  rw [integral_sub first second,integral_smul_const,slopeRead]
  module

private theorem primitive_partition (primitive : ℝ → BurnolL2)
    (continuous : ContinuousOn primitive (Ioi 0)) (lower middle upper : ℝ)
    (positive : 0<lower) (lowerMiddle : lower≤middle) (middleUpper : middle≤upper)
    (weight slope : ℝ → ℂ)
    (derivative : ∀ u∈Icc lower upper, HasDerivAt weight (slope u) u)
    (regular : ContinuousOn slope (Icc lower upper)) :
    primitiveStep primitive lower upper weight slope=
      primitiveStep primitive middle upper weight slope+
        primitiveStep primitive lower middle weight slope := by
  have smallRegular:=regular.mono (Icc_subset_Icc le_rfl middleUpper)
  have largeRegular:=regular.mono (Icc_subset_Icc lowerMiddle le_rfl)
  have smallDerivative:=fun u inside=>derivative u (Icc_subset_Icc le_rfl middleUpper inside)
  have largeDerivative:=fun u inside=>derivative u (Icc_subset_Icc lowerMiddle le_rfl inside)
  rw [primitive_stock primitive continuous lower upper positive (lowerMiddle.trans middleUpper)
      weight slope derivative regular,
    primitive_stock primitive continuous middle upper (positive.trans_le lowerMiddle) middleUpper
      weight slope largeDerivative largeRegular,
    primitive_stock primitive continuous lower middle positive lowerMiddle
      weight slope smallDerivative smallRegular]
  have integralRegular:ContinuousOn (fun u=>slope u • primitive u) (Icc lower upper):=
    regular.smul (continuous.mono (fun _ inside=>positive.trans_le inside.1))
  have whole:(∫ u : ℝ in Ioc lower upper,slope u • primitive u)=
      (∫ u : ℝ in Ioc lower middle,slope u • primitive u)+
        ∫ u : ℝ in Ioc middle upper,slope u • primitive u := by
    simp_rw [← intervalIntegral.integral_of_le (lowerMiddle.trans middleUpper),
      ← intervalIntegral.integral_of_le lowerMiddle,← intervalIntegral.integral_of_le middleUpper]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((integralRegular.mono (Icc_subset_Icc le_rfl middleUpper)).intervalIntegrable_of_Icc lowerMiddle)
      ((integralRegular.mono (Icc_subset_Icc lowerMiddle le_rfl)).intervalIntegrable_of_Icc middleUpper)).symm
  rw [whole]
  module

private theorem primitive_weight_difference (primitive : ℝ → BurnolL2)
    (continuous : ContinuousOn primitive (Ioi 0)) (lower upper : ℝ) (positive : 0<lower)
    (oldWeight nextWeight oldSlope nextSlope : ℝ → ℂ)
    (oldRegular : ContinuousOn oldSlope (Icc lower upper))
    (nextRegular : ContinuousOn nextSlope (Icc lower upper)) :
    primitiveStep primitive lower upper nextWeight nextSlope-
        primitiveStep primitive lower upper oldWeight oldSlope=
      primitiveStep primitive lower upper (fun u=>nextWeight u-oldWeight u)
        (fun u=>nextSlope u-oldSlope u) := by
  have primitiveContinuous:ContinuousOn (fun u=>primitive u-primitive lower) (Icc lower upper):=
    (continuous.mono (fun _ inside=>positive.trans_le inside.1)).sub continuousOn_const
  have first:IntegrableOn (fun u=>nextSlope u • (primitive u-primitive lower)) (Ioc lower upper):=
    (nextRegular.smul primitiveContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have second:IntegrableOn (fun u=>oldSlope u • (primitive u-primitive lower)) (Ioc lower upper):=
    (oldRegular.smul primitiveContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  unfold primitiveStep
  simp_rw [sub_smul]
  rw [integral_sub first second]
  module

def weightUpdate
    (native : ℝ → ℝ → (ℝ → ℂ) → (ℝ → ℂ) → BurnolL2)
    (weight slope : ℝ → ℝ → ℂ) (h nextShift : ℝ) : BurnolL2 :=
  native (NativeWeight.bandLower h) 4 (fun u=>weight nextShift u-weight h u)
      (fun u=>slope nextShift u-slope h u)+
    native (NativeWeight.bandLower nextShift) (NativeWeight.bandLower h) (weight nextShift) (slope nextShift)

private theorem bandLower_antitone (h nextShift : ℝ) (ordered : h≤nextShift) :
    NativeWeight.bandLower nextShift≤NativeWeight.bandLower h := by
  unfold NativeWeight.bandLower
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ordered)) (by norm_num)

private theorem primitive_parameter_update (primitive : ℝ → BurnolL2)
    (continuous : ContinuousOn primitive (Ioi 0)) (h nextShift : ℝ)
    (nonnegative : 0≤h) (ordered : h≤nextShift) (weight slope : ℝ → ℝ → ℂ)
    (derivative : ∀ t u,0<u → HasDerivAt (weight t) (slope t u) u)
    (regular : ∀ t,ContinuousOn (slope t) (Ioi 0)) :
    primitiveStep primitive (NativeWeight.bandLower nextShift) 4 (weight nextShift) (slope nextShift)-
        primitiveStep primitive (NativeWeight.bandLower h) 4 (weight h) (slope h)=
      weightUpdate (primitiveStep primitive) weight slope h nextShift := by
  have lowerMiddle:=bandLower_antitone h nextShift ordered
  have middleUpper:=NativeWeight.bandLower_le_four h nonnegative
  have positive:=NativeWeight.bandLower_pos nextShift
  rw [primitive_partition primitive continuous _ _ _ positive lowerMiddle middleUpper
    (weight nextShift) (slope nextShift)
    (fun u inside=>derivative nextShift u (positive.trans_le inside.1))
    ((regular nextShift).mono (fun _ inside=>positive.trans_le inside.1))]
  unfold weightUpdate
  rw [← primitive_weight_difference primitive continuous _ _ (NativeWeight.bandLower_pos h)
    (weight h) (weight nextShift) (slope h) (slope nextShift)
    ((regular h).mono (fun _ inside=>(NativeWeight.bandLower_pos h).trans_le inside.1))
    ((regular nextShift).mono (fun _ inside=>(NativeWeight.bandLower_pos h).trans_le inside.1))]
  module

def positionWaveUpdate (coordinate : BurnolCompletedMellinCoordinate) (h nextShift : ℝ) : BurnolL2 :=
  weightUpdate burnolWeightedReciprocalStepWave (NativeWeight.positionWeight coordinate)
    (fun t=>deriv (NativeWeight.positionWeight coordinate t)) h nextShift
def fourierWaveUpdate (coordinate : BurnolCompletedMellinCoordinate) (h nextShift : ℝ) : BurnolL2 :=
  weightUpdate burnolWeightedReciprocalStepWave (NativeWeight.fourierWeight coordinate)
    (fun t=>deriv (NativeWeight.fourierWeight coordinate t)) h nextShift
def positionSeedUpdate (coordinate : BurnolCompletedMellinCoordinate) (h nextShift : ℝ) : BurnolL2 :=
  weightUpdate burnolWeightedReciprocalStepSource (NativeWeight.positionWeight coordinate)
    (fun t=>deriv (NativeWeight.positionWeight coordinate t)) h nextShift
def fourierSeedUpdate (coordinate : BurnolCompletedMellinCoordinate) (h nextShift : ℝ) : BurnolL2 :=
  weightUpdate burnolWeightedReciprocalStepSource (NativeWeight.fourierWeight coordinate)
    (fun t=>deriv (NativeWeight.fourierWeight coordinate t)) h nextShift

theorem actual_native_position_update (coordinate : BurnolCompletedMellinCoordinate)
    (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) :
    PaidWave.positionWave coordinate nextShift-PaidWave.positionWave coordinate h=positionWaveUpdate coordinate h nextShift ∧
    Seed.positionSeed coordinate nextShift-Seed.positionSeed coordinate h=positionSeedUpdate coordinate h nextShift := by
  constructor
  · exact primitive_parameter_update (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2)
      (burnolSourceScalePrimitive_continuous _) h nextShift nonnegative ordered
      (NativeWeight.positionWeight coordinate) (fun t=>deriv (NativeWeight.positionWeight coordinate t))
      (NativeWeight.positionWeight_hasDerivAt coordinate) (NativeWeight.positionWeight_deriv_continuousOn coordinate)
  · exact primitive_parameter_update (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2)
      (burnolSourceScalePrimitive_continuous _) h nextShift nonnegative ordered
      (NativeWeight.positionWeight coordinate) (fun t=>deriv (NativeWeight.positionWeight coordinate t))
      (NativeWeight.positionWeight_hasDerivAt coordinate) (NativeWeight.positionWeight_deriv_continuousOn coordinate)

theorem actual_native_fourier_update (coordinate : BurnolCompletedMellinCoordinate)
    (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) :
    PaidWave.fourierWave coordinate nextShift-PaidWave.fourierWave coordinate h=fourierWaveUpdate coordinate h nextShift ∧
    Seed.fourierSeed coordinate nextShift-Seed.fourierSeed coordinate h=fourierSeedUpdate coordinate h nextShift := by
  constructor
  · exact primitive_parameter_update (burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2)
      (burnolSourceScalePrimitive_continuous _) h nextShift nonnegative ordered
      (NativeWeight.fourierWeight coordinate) (fun t=>deriv (NativeWeight.fourierWeight coordinate t))
      (NativeWeight.fourierWeight_hasDerivAt coordinate) (NativeWeight.fourierWeight_deriv_continuousOn coordinate)
  · exact primitive_parameter_update (burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2)
      (burnolSourceScalePrimitive_continuous _) h nextShift nonnegative ordered
      (NativeWeight.fourierWeight coordinate) (fun t=>deriv (NativeWeight.fourierWeight coordinate t))
      (NativeWeight.fourierWeight_hasDerivAt coordinate) (NativeWeight.fourierWeight_deriv_continuousOn coordinate)

def upperWaveNativeUpdate (coordinate : BurnolCompletedMellinCoordinate) (h nextShift : ℝ) : BurnolL2 :=
  (upperSeedFactor nextShift-upperSeedFactor h) •
      (PaidWave.positionWave coordinate h+fourierL2 (PaidWave.fourierWave coordinate h))+
    upperSeedFactor nextShift • (positionWaveUpdate coordinate h nextShift+fourierL2 (fourierWaveUpdate coordinate h nextShift))
def upperFieldNativeUpdate (coordinate : BurnolCompletedMellinCoordinate) (h nextShift : ℝ) : BurnolL2 :=
  (upperSeedFactor nextShift-upperSeedFactor h) •
      (Seed.positionSeed coordinate h+fourierL2 (Seed.fourierSeed coordinate h))+
    upperSeedFactor nextShift • (positionSeedUpdate coordinate h nextShift+fourierL2 (fourierSeedUpdate coordinate h nextShift))

theorem actual_upper_material_update (coordinate : BurnolCompletedMellinCoordinate)
    (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) :
    upperSourceWave coordinate nextShift-upperSourceWave coordinate h=upperWaveNativeUpdate coordinate h nextShift ∧
    upperSourceField coordinate nextShift-upperSourceField coordinate h=upperFieldNativeUpdate coordinate h nextShift := by
  obtain ⟨positionWave,positionSeed⟩:=actual_native_position_update coordinate h nextShift nonnegative ordered
  obtain ⟨fourierWave,fourierSeed⟩:=actual_native_fourier_update coordinate h nextShift nonnegative ordered
  constructor
  · unfold upperSourceWave upperWaveNativeUpdate
    rw [← positionWave,← fourierWave,map_sub]
    module
  · rw [actual_upper_common_seed coordinate nextShift (nonnegative.trans ordered),
      actual_upper_common_seed coordinate h nonnegative]
    unfold upperFieldNativeUpdate
    rw [← positionSeed,← fourierSeed,map_sub]
    module

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
