import H0mework.Fock.CopyGraph.Moments
import H0mework.Fock.HistoryPolynomial.CopyEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceSuccessorBoundary SourceCyclicModule
noncomputable section

theorem root_clock : SourceJointClockGraph.clock (SourceJointClockGraph.read (SourceClockComplex.ofNative (program 1))) = 1 := by
  rw [SourceJointClockGraph.clock_source, program_one, original_root]
  change SourceClockComplex.clock (SourceClockComplex.ofNative (Finsupp.single 0 1)) = 1
  rw [SourceClockComplex.ofNative_single, SourceClockComplex.clock_single]
  norm_num [SourceClockModel.rawClock]

theorem root_energy (depth : Nat) (index : Index depth) :
    ‖action depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative (program 1)))‖ ^ 2 =
      ‖SourceJointClockGraph.read (SourceClockComplex.ofNative (program 1))‖ ^ 2 + (scale depth index : ℝ) ^ 2 - 1 := by
  rw [action_energy, root_clock, norm_one, one_pow, mul_one]
  ring

theorem action_not_isometry (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    ¬ ∀ value : SourceJointClockGraph.Carrier, ‖action depth index value‖ = ‖value‖ := by
  intro preserves
  have source := root_energy depth index
  rw [preserves] at source
  have amount : (1 : ℝ) < scale depth index := by
    have amount : 1 < scale depth index := by rw [scale_source]; omega
    exact_mod_cast amount
  nlinarith

theorem native_residual_moments_retained (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    residual depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative (program 1))) + axes 1 1 =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (program 1)) := by
  have source := residual_native_moments depth index (program 1)
  rw [SourceCopyProgram.nonunit_root_residual depth index nonunit] at source
  have sourceMass : mass ℂ (SourceClockComplex.ofNative (program 1)) = 1 := by
    rw [program_one, original_root]
    change mass ℂ (SourceClockComplex.ofNative (Finsupp.single 0 1)) = 1
    rw [SourceClockComplex.ofNative_single, mass_single]
    norm_num
  have sourceClock : SourceClockComplex.clock (SourceClockComplex.ofNative (program 1)) = 1 := root_clock
  rw [sourceMass, sourceClock] at source
  exact source

theorem residual_not_native_residual (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    residual depth index (SourceJointClockGraph.read (SourceClockComplex.ofNative (program 1))) ≠
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCopyProgram.residual depth index (program 1))) := by
  intro same
  rw [SourceCopyProgram.nonunit_root_residual depth index nonunit] at same
  have source := native_residual_moments_retained depth index nonunit
  rw [same] at source
  have lost : axes 1 1 = 0 := add_left_cancel (source.trans (add_zero _).symm)
  have observed := congrArg SourceJointClockGraph.clock lost
  change (1 : ℂ) = 0 at observed
  exact one_ne_zero observed

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
