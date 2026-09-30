import H0mework.Versions.X.NavierStokes.WindowPhysics.RootCarrier
import H0mework.Versions.X.NavierStokes.SourceHeat.PairingAverage

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowRootPairing

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current}

def data (_carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) : NativeStressPairingCarrier.Data :=
  NativeHeatPairingAverage.sourceData initial query.1 (clockAt initial current + time)

theorem data_mean (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    (data carrier query time).mean = (carrier.view query.1 time).fst := by
  rw [data, NativeHeatPairingAverage.source_mean, CarrierAt.view_generated]
  rfl

theorem data_stress (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    (data carrier query time).stress = NativeCompleteStressCarrier.read (carrier.view query.1 time).snd := by
  rw [data, NativeHeatPairingAverage.source_stress, CarrierAt.view_generated]
  rfl

theorem data_residual (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    (data carrier query time).stress - NativeStressSource.quadraticFlux (wholeVelocity (data carrier query time).mean) =
      NativeCompleteCorrectionRead.residual (carrier.view query.1 time) := by
  rw [data_mean, data_stress]
  rfl

theorem canonical_current (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ)
    (direction : Fin 4) (wave : IntegerWavevector) :
    NativeHilbertDiracCurrent.diracCurrent (data carrier query time) direction wave =
      NativePairedCurrentFourier.coefficient (wholeVelocity (carrier.view query.1 time).fst)
        (NativeCompleteStressCarrier.read (carrier.view query.1 time).snd) direction wave := by
  rw [data, NativeHeatPairingAverage.source_diracCurrent, CarrierAt.view_generated]
  rfl

theorem data_ext (first last : NativeStressPairingCarrier.Data)
    (mean : first.mean = last.mean) (stress : first.stress = last.stress) : first = last := by
  cases first
  cases last
  cases mean
  cases stress
  rfl

theorem data_eq_of_view_eq {lastCurrent : NativeTemporalCurrent initial} {lastOccurrence : Occurrence initial lastCurrent}
    (first : CarrierAt initial occurrence) (last : CarrierAt initial lastOccurrence) (query : HeatQuery) (a b : ℝ)
    (same : first.view query.1 a = last.view query.1 b) : data first query a = data last query b := by
  apply data_ext
  · rw [data_mean, data_mean, same]
  · rw [data_stress, data_stress, same]

theorem finite_next_pairing (initial : GeneratedWholeRestartCurrent nu) (index : ℕ) (query : HeatQuery) (time : ℝ) :
    data (generatedCarrier initial (nativeTemporalEmitted initial (.finite (index + 1)))) query time =
      data (generatedCarrier initial (nativeTemporalEmitted initial (.finite index))) query
        ((run initial index).contact.time.1 + time) :=
  data_eq_of_view_eq _ _ query _ _ (finite_next_view initial index query time)

theorem cofinal_next_pairing (initial : GeneratedWholeRestartCurrent nu) (query : HeatQuery) (time : ℝ) :
    data (generatedCarrier initial (nativeTemporalEmitted initial (.galerkin 0))) query time =
      data (generatedCarrier initial (nativeTemporalEmitted initial .cofinal)) query time :=
  data_eq_of_view_eq _ _ query _ _ (congrFun (cofinal_next_view initial query) time)

theorem galerkin_next_pairing (initial : GeneratedWholeRestartCurrent nu) (radius : ℕ) (query : HeatQuery) (time : ℝ) :
    data (generatedCarrier initial (nativeTemporalEmitted initial (.galerkin (radius + 1)))) query time =
      data (generatedCarrier initial (nativeTemporalEmitted initial (.galerkin radius))) query time :=
  data_eq_of_view_eq _ _ query _ _ (congrFun (galerkin_next_view initial radius query) time)

end
end SaturationMonoid.NavierStokes.NativeWindowRootPairing
