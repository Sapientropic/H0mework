import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mean.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Adjoint

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mean.Consumer
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward OriginalPaPhysicalGreen
open OriginalRieszSourceGreen
open OriginalKSourceResolventReconstruction OriginalKCrossParameterRAdjointSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mean.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Adjoint
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "C" => ConstantDual.seed
local notation "K" => burnolCompletedMellinRieszVector

theorem actual_wave_mass (c:BurnolCompletedMellinCoordinate) :
    inner ℂ C (quarterWave c) =
      (1/(Real.pi:ℂ))*HurwitzZeta.sinZeta q (star c.value+1) := by
  have mean := actual_quarter_mean c
  unfold burnolQuarterMeanCoefficient at mean
  rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)] at mean
  change inner ℂ (burnolQuarterZeroExtension (intervalConstant q))
    (burnolQuarterZeroExtension (periodicQuarter c)) = _
  rw [quarter_extension_inner]
  norm_num only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_div,Complex.ofReal_one] at mean
  linear_combination (1/2:ℂ)*mean

/-- The actual centered Euler source retains the computed Unit and both boundary contacts. -/
theorem actual_centered_unit_euler (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) :
    GapEuler.euler (centeredWave c:TemperedDistribution ℝ ℂ)=
      (star c.value-1/2) • (centeredWave c:TemperedDistribution ℝ ℂ)+
      (companion c:TemperedDistribution ℝ ℂ)+
      (star c.value*((2/(Real.pi:ℂ))*HurwitzZeta.sinZeta q (star c.value+1))) •
        (C:TemperedDistribution ℝ ℂ)+
      ((2/(Real.pi:ℂ))*HurwitzZeta.sinZeta q (star c.value+1)) • GapEuler.edge q := by
  have generated := actual_centered_euler c zero
  rw [quarterMean,actual_quarter_mean] at generated
  exact generated

/-- The two independent original adjoints consume the literal sine-zeta Unit price. -/
theorem actual_two_adjoint_unit_prices (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) :
    (1/2:ℂ)*inner ℂ (sourceFKResponse c c) (companion c)=
      star (fourierMean c)*((1/(Real.pi:ℂ))*HurwitzZeta.sinZeta q (star c.value+1)) ∧
    (1/2:ℂ)*inner ℂ (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2)) (companion c)=
      star (positionMean c)*((1/(Real.pi:ℂ))*HurwitzZeta.sinZeta q (star c.value+1)) := by
  simpa only [actual_wave_mass] using actual_original_two_adjoint_prices c zero

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mean.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
