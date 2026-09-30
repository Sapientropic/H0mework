import H0mework.Versions.X.Fock.PrimeField.ClockSplittingAction

/-! Original finite source words keep their clock coordinate; the new section does not replace native occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeClockResidual
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

theorem clock_source (source : SourceOperationNative.Carrier process) :
    clockRead (sourceMap nativeAction jointObservation source) = SourceClockModel.clock source := by
  have read := source_reads_stage nativeAction jointObservation 0 source (0 : Fin 1)
  change stageRead nativeAction jointObservation 0 (sourceMap nativeAction jointObservation source) 0 = jointObservation source at read
  have pair := LinearMap.congr_fun observation_joint source
  exact congrArg Prod.snd (read.trans pair)

theorem source_coordinates (source : SourceOperationNative.Carrier process) :
    coordinates (sourceMap nativeAction jointObservation source) =
      (sourceMap nativeAction observation source, SourceClockModel.clock source) :=
  Prod.ext (projection_source source) (clock_source source)

theorem source_reconstruction (source : SourceOperationNative.Carrier process) :
    rebuild (sourceMap nativeAction observation source, SourceClockModel.clock source) =
      sourceMap nativeAction jointObservation source := by
  exact (congrArg rebuild (source_coordinates source)).symm.trans (rebuild_coordinates _)

theorem source_section_fibre (source : SourceOperationNative.Carrier process) :
    let native : JointField := sourceMap nativeAction jointObservation source
    native - sectionMap (sourceMap nativeAction observation source) =
      SourceClockModel.clock source • SourcePrimeClockResidual.residual := by
  have fibre := (fibre_exact (sourceMap nativeAction jointObservation source)
    (sectionMap (sourceMap nativeAction observation source))).mp
    ((projection_source source).trans (section_prime _).symm)
  have clockZero : clockRead (sectionMap (sourceMap nativeAction observation source)) = 0 := section_clock _
  simpa only [clock_source, clockZero, sub_zero] using fibre

theorem native_coordinates (current : LivingRuntimeState process) :
    coordinates (fieldPoint (process := process) jointRead current.state) =
      (fieldPoint (process := process) rawField current.state, SourceClockModel.rawClock current.state) :=
  (source_coordinates (SourceOperationNative.point current)).trans
    (congrArg (fun clock => (fieldPoint (process := process) rawField current.state, clock))
      (SourceOperationNative.observer_point SourceClockModel.rawClock current))

theorem unit_section_not_source : ¬ ∃ source : SourceOperationNative.Carrier process,
    sourceMap nativeAction jointObservation source = sectionMap (fieldPoint (process := process) rawField 0) := by
  rintro ⟨source, sourceEq⟩
  have projected := congrArg primeProjection sourceEq
  rw [projection_source, section_prime] at projected
  have same : source = SourceOperationNative.statePoint process 0 :=
    SourcePrimeHistoryRecovery.sourceMap_injective sourceOwner projected
  have clocks := congrArg clockRead sourceEq
  rw [clock_source, section_clock, same] at clocks
  change SourceClockModel.clock (Finsupp.single 0 1) = 0 at clocks
  rw [SourceClockModel.clock_single] at clocks
  norm_num at clocks

theorem unit_section_action_defect :
    clockRead (fieldAction (process := process) jointRead (sectionMap (fieldPoint (process := process) rawField 0))) = 1 ∧
      clockRead (sectionMap (fieldAction (process := process) rawField (fieldPoint (process := process) rawField 0))) = 0 := by
  exact ⟨(clock_zero_section_defect _).trans SourcePrimeCompletion.original_unit_mass, section_clock _⟩

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
