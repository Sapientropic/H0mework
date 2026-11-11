import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.NativeRegular
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactC1
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.NativeRegular OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace ContDiff
open private fourier_raw_even_of_fixed from
  H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "E"=>burnolQuarterZeroExtension
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "H"=>burnolUnitCountingPrimitiveL2

def nativeProgramme (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  InfiniteWeightedProgram.program (deriv (weight (nativeRaw c))) H

def logProgramme (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  InfiniteWeightedProgram.program (deriv (weight (burnolMeanZeroFourierRaw (logBFirst c 0)))) H

private theorem native_inputs (c:BurnolCompletedMellinCoordinate):
    (∀u:ℝ,4≤u→HasDerivAt (weight (nativeRaw c)) (deriv (weight (nativeRaw c)) u) u)∧
      ContinuousOn (deriv (weight (nativeRaw c))) (Ici 4)∧Measurable (weight (nativeRaw c))∧
      IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight (nativeRaw c)))) (Ioi 4)∧
      Tendsto (fun u:ℝ=>Real.sqrt u*‖weight (nativeRaw c) u‖) atTop (𝓝 0):=
  actual_compact_c1_inputs (nativeCompact c) (nativeRaw c) (nativeSlope c)
    (actual_native_compact_raw c) (fun x _=>actual_native_absolute c x) (actual_native_measurable c)
    (actual_native_continuous c) (actual_native_slope_continuous c)
    (fun x positive bounded=>actual_native_derivative c x ⟨positive,bounded⟩)

/-- The full finite continuous programme, including the original H−B origin value, has this actual strong limit. -/
theorem actual_native_forward (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (nativeCompact c))) atTop (𝓝 (nativeProgramme c)):=by
  obtain ⟨hd,hcont,hmeas,hdom,hhead⟩:=native_inputs c
  exact actual_compact_forward (nativeCompact c) (nativeRaw c) (actual_native_compact_raw c)
    (fun x _=>actual_native_absolute c x) hd hcont hmeas hdom hhead

/-- The independent reverse uses the same actual compact input and the same nonzero constant primitive. -/
theorem actual_native_reverse (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun N:ℕ=>DualSource.source N (E (nativeCompact c))) atTop
      (𝓝 (poissonPair (nativeProgramme c))):=by
  obtain ⟨hd,hcont,_hmeas,hdom,hhead⟩:=native_inputs c
  exact actual_compact_reverse (nativeCompact c) (nativeRaw c) (actual_native_compact_raw c)
    (fun x _=>actual_native_absolute c x) hd hcont hdom hhead

/-- This is the whole Schwartz realization of that very same strong programme. -/
theorem actual_native_realizes (c:BurnolCompletedMellinCoordinate) (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (E (nativeCompact c)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (nativeProgramme c)) test:=by
  obtain ⟨hd,hcont,_hmeas,hdom,hhead⟩:=native_inputs c
  exact actual_compact_realizes (nativeCompact c) (nativeRaw c) (actual_native_compact_raw c)
    (fun x _=>actual_native_absolute c x) hd hcont hdom hhead test

private theorem log_inputs (c:BurnolCompletedMellinCoordinate):
    (∀u:ℝ,4≤u→HasDerivAt (weight (burnolMeanZeroFourierRaw (logBFirst c 0)))
      (deriv (weight (burnolMeanZeroFourierRaw (logBFirst c 0))) u) u)∧
      ContinuousOn (deriv (weight (burnolMeanZeroFourierRaw (logBFirst c 0)))) (Ici 4)∧
      Measurable (weight (burnolMeanZeroFourierRaw (logBFirst c 0)))∧
      IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight (burnolMeanZeroFourierRaw (logBFirst c 0))))) (Ioi 4)∧
      Tendsto (fun u:ℝ=>Real.sqrt u*‖weight (burnolMeanZeroFourierRaw (logBFirst c 0)) u‖) atTop (𝓝 0):=by
  let raw:=burnolMeanZeroFourierRaw (logBFirst c 0)
  have smooth:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative.actual_return_contDiff (logBFirst c 0)
  have fixed:reflectRestricted q (logBFirst c 0:Hq)=(logBFirst c 0:Hq):=
    congrArg (fun state:BurnolQuarterMeanZeroCarrier=>(state:Hq)) (log_B_even c 0)
  have even (x:ℝ):raw (-x)=raw x:=by
    dsimp only [raw,burnolMeanZeroFourierRaw]
    rw [fourier_raw_even_of_fixed _ fixed x]
  exact actual_compact_c1_inputs (S (logBFirst c 0):Hq) raw (deriv raw)
    (burnolMeanZeroFourier_ae_raw (logBFirst c 0))
    (fun x _=>by
      by_cases positive:0≤x
      · rw [abs_of_nonneg positive]
      · rw [abs_of_neg (lt_of_not_ge positive),even])
    smooth.continuous.measurable smooth.continuous.continuousOn
    (smooth.continuous_deriv (by norm_num)).continuousOn
    (fun x _ _=>((smooth.differentiable (by norm_num)) x).hasDerivAt)

theorem actual_log_return_reverse (c:BurnolCompletedMellinCoordinate):
    Tendsto (fun N:ℕ=>DualSource.source N (E (S (logBFirst c 0):Hq))) atTop
      (𝓝 (poissonPair (logProgramme c))):=by
  obtain ⟨hd,hcont,_hmeas,hdom,hhead⟩:=log_inputs c
  have fixed:reflectRestricted q (logBFirst c 0:Hq)=(logBFirst c 0:Hq):=
    congrArg (fun state:BurnolQuarterMeanZeroCarrier=>(state:Hq)) (log_B_even c 0)
  apply actual_compact_reverse (S (logBFirst c 0):Hq) (burnolMeanZeroFourierRaw (logBFirst c 0))
    (burnolMeanZeroFourier_ae_raw (logBFirst c 0)) _ hd hcont hdom hhead
  intro x _
  by_cases positive:0≤x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive)]
    simp only [burnolMeanZeroFourierRaw,fourier_raw_even_of_fixed _ fixed x]

theorem actual_log_return_realizes (c:BurnolCompletedMellinCoordinate) (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (E (S (logBFirst c 0):Hq)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (logProgramme c)) test:=by
  obtain ⟨hd,hcont,_hmeas,hdom,hhead⟩:=log_inputs c
  have fixed:reflectRestricted q (logBFirst c 0:Hq)=(logBFirst c 0:Hq):=
    congrArg (fun state:BurnolQuarterMeanZeroCarrier=>(state:Hq)) (log_B_even c 0)
  apply actual_compact_realizes (S (logBFirst c 0):Hq) (burnolMeanZeroFourierRaw (logBFirst c 0))
    (burnolMeanZeroFourier_ae_raw (logBFirst c 0)) _ hd hcont hdom hhead test
  intro x _
  by_cases positive:0≤x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive)]
    simp only [burnolMeanZeroFourierRaw,fourier_raw_even_of_fixed _ fixed x]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
