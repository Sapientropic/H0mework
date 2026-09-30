import H0mework.NavierStokes.WindowSchurMean.PhysicalJet
import H0mework.NavierStokes.WindowSchurFrozen.HeatDual
import H0mework.NavierStokes.UnheatedWriterSobolev.Velocity
import H0mework.NavierStokes.WindowHistoryCreation.Geometry

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanJetEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryMeanPhysicalJet (physicalJet includeState)
open NativeWindowHistoryHeatDual (energy)
open NativeEndpointVelocityCarrier (wholeVelocity)
open NativeForwardWindowEvolution (velocityJet)
noncomputable section
variable {nu : Viscosity}

theorem whole_read (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    (physicalJet seed M order time).1=wholeVelocity (NativeWindowHistoryMeanTime.jet seed M order time) := by
  have source:=congrArg wholeVelocity (NativeWindowHistoryMeanPhysicalJet.includeState_jet seed M order time)
  change wholeVelocity (puncturedEuclideanize (physicalJet seed M order time).1)=_ at source
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _
    (physical_supported (physicalJet seed M order time) 0 (modes_zero M))] at source
  exact source

theorem row_inside (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (included : wave∈modes M) :
    (physicalJet seed M order time).1 wave=wholeVelocity (velocityJet seed order time) wave := by
  have zero:wave≠0:=fun eq => modes_zero M (eq ▸ included)
  have covered:wave∈ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay.wholeRestartModes M:=included
  rw [whole_read]
  funext i
  rw [NativeWindowHistoryMeanTime.jet,NativeWindowHistoryMeanTime.read_original,
    NativeEndpointVelocityCarrier.wholeVelocity_nonzero _ ⟨wave,zero⟩,
    wholeRestartVelocityEndpointGalerkinInitialVelocity_apply,if_pos covered,
    NativeEndpointVelocityCarrier.wholeVelocity_nonzero _ ⟨wave,zero⟩]

private theorem weight_lower (frequency : ℝ) (nonnegative : 0 ≤ frequency) :
    frequency ≤ (1+frequency)*Real.sqrt (1+frequency) := by
  have root:=Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1+frequency by linarith)
  rw [Real.sqrt_one] at root
  exact (show frequency ≤ 1+frequency by linarith).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left root (by linarith : 0 ≤ 1+frequency))

theorem source_gradient (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    curlPair (modes M) (physicalJet seed M order time).1 (physicalJet seed M order time).1 ≤
      (2*Real.pi)^2*NativeWindowSobolevVelocity.budget seed order horizon := by
  have valid:-1 < time:=by linarith [inside.1]
  have row (wave : IntegerWavevector) (included : wave∈modes M) :
      integerWaveNormSq wave*(∑ i : Coordinate,‖(physicalJet seed M order time).1 wave i‖^2) ≤
        NativeWindowSobolevVelocity.wholeDensity seed order time wave := by
    rw [row_inside seed M order time wave included]
    have bound:=mul_le_mul_of_nonneg_right (weight_lower (integerWaveNormSq wave) (integerWaveNormSq_nonneg wave))
      (Finset.sum_nonneg fun i (_ : i∈(Finset.univ : Finset Coordinate)) => sq_nonneg ‖wholeVelocity (velocityJet seed order time) wave i‖)
    simpa only [NativeWindowSobolevVelocity.wholeDensity,complexCoordinateAmplitudeSq,Complex.normSq_eq_norm_sq] using bound
  have positive (wave : IntegerWavevector) : 0 ≤ NativeWindowSobolevVelocity.wholeDensity seed order time wave := by
    unfold NativeWindowSobolevVelocity.wholeDensity complexCoordinateAmplitudeSq
    simp only [Complex.normSq_eq_norm_sq]
    have frequency:=integerWaveNormSq_nonneg wave
    positivity
  have full:=(NativeWindowSobolevVelocity.whole_summable seed order time valid).sum_le_tsum
    (s := modes M) (fun wave _ => positive wave)
  have paid:=(Finset.sum_le_sum row).trans (full.trans (NativeWindowSobolevVelocity.whole_bound_on_interval seed order time horizon valid inside.2))
  rw [NativeWindowHistoryCreationGeometry.curl_mass (modes M) (modes_zero M)]
  exact mul_le_mul_of_nonneg_left paid (sq_nonneg _)

def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  NativeForwardWindowJets.budget seed order^2+nu.coeff*(2*Real.pi)^2*NativeWindowSobolevVelocity.budget seed order horizon

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : 0 ≤ budget seed order horizon := by
  have viscosity:=nu.coeff_pos
  unfold budget NativeWindowSobolevVelocity.budget
  positivity

theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    energy nu M (physicalJet seed M order time) ≤ budget seed order horizon := by
  have mass:=pow_le_pow_left₀ (norm_nonneg _) (NativeWindowHistoryMeanPhysicalJet.physicalJet_norm seed M order time) 2
  have gradient:=mul_le_mul_of_nonneg_left (source_gradient seed order horizon M time inside) nu.coeff_pos.le
  exact (add_le_add mass gradient).trans_eq (by unfold budget; ring)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem energy_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    energy nu M (physicalJet seed M order (step.2.clockAdvance+time))=energy nu M (physicalJet step.1 M order time) :=
  congrArg (energy nu M) (NativeWindowHistoryMeanPhysicalJet.physicalJet_next seed M order step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanJetEnergy
