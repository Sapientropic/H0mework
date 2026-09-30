import H0mework.Versions.X.Fock.HistoryConditional.GWordInverseClock

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordInverse

open SourceGeneratedActionWords SourceCopyTimeModel SourceOwnedObservationHistory.SourceShift SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem native_hilbert_recover (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    hilbert (recover depth word (SourceJointClockGraph.read (SourceClockComplex.ofNative source))) =
      readWord (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source)) := by
  ext coordinate
  rw [hilbert_recover]
  change readWord (SourceClockComplex.ofNative source) _ = _
  rw [SourceCopyGraph.native_hilbert, SourceCopyGraph.native_hilbert, wordRead_coordinate, wordRead_coordinate,
    SourceCompiledWordOperator.recovery_reads]

theorem native_mass_balance (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    mass (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source))) +
      mass (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source))) =
        mass (SourceJointClockGraph.read (SourceClockComplex.ofNative source)) := by
  have paid := congrArg (fun value => SourceVectorMoment.massMap (SourceJointClockGraph.read (SourceClockComplex.ofNative value)))
    (SourceCompiledWordOperator.reconstruct depth word source)
  rw [map_add, map_add, map_add, ← SourceCompiledGWord.source_effect] at paid
  change mass (SourceCompiledGWord.effect depth word
    (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source)))) + _ = _ at paid
  rw [SourceCompiledGWord.mass_effect] at paid
  exact paid

theorem native_clock_balance (depth : Nat) (word : List (Fock.Letter depth)) (source : SourceOperationNative.Carrier process) :
    ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℂ) *
      SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source))) +
    ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 : ℂ) *
      mass (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.recover depth word source))) +
      SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCompiledWordOperator.residual depth word source))) =
        SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative source)) := by
  have paid := congrArg (fun value => SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative value)))
    (SourceCompiledWordOperator.reconstruct depth word source)
  rw [map_add, map_add, map_add, ← SourceCompiledGWord.source_effect, SourceCompiledGWord.clock_effect] at paid
  exact paid

end
end SourceGWordInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
