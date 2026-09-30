import H0mework.Fock.CopyGraph.TimeModelFinite

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index scale indexAfter)
noncomputable section

def blind (depth : Nat) (index : Index depth) : SourceJointClockGraph.Carrier :=
  SourceCopyGraph.residual depth index
    (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCyclicModule.program 1)))

theorem blind_read_zero (depth : Nat) (index : Index depth) : SourceCopyGraph.recover depth index (blind depth index) = 0 :=
  SourceCopyRecoveryBudget.recover_residual_zero depth index _

theorem blind_coordinate (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    hilbert (blind depth index) 0 = 1 := by
  have source := SourceCopyGraph.native_residual_moments_retained depth index nonunit
  have coordinate := congrArg (fun value : SourceJointClockGraph.Carrier => hilbert value 0) source
  simp only [hilbert, map_add, lp.coeFn_add, Pi.add_apply] at coordinate
  change hilbert (blind depth index) 0 + 0 = SourceMassCompletion.firstRead
    (SourceJointClockGraph.joint (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceCyclicModule.program 1)))) 0 at coordinate
  rw [add_zero, SourceJointClockGraph.joint_source, SourceMassCompletion.firstRead_source, SourceCopyGraph.native_hilbert,
    SourceOwnedObservationHistory.SourceShift.wordRead_coordinate, SourceCyclicModule.program_one,
    SourceCyclicModule.original_root] at coordinate
  change hilbert (blind depth index) 0 = ((Finsupp.single 0 (1 : ℤ)) 0 : ℂ) at coordinate
  simpa only [Finsupp.single_eq_same, Int.cast_one] using coordinate

theorem blind_later_coordinate (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    hilbert (phases depth index (blind depth index) (Fin.last index.val)) 0 = 1 := by
  rw [phase_source, recover_hilbert]
  have address : indexAfter depth index 0 = index.val := by
    have source := SourceCopyProgram.index_exact depth index 0
    rw [SourceCopyProgram.scale_source] at source
    simp only [Nat.zero_add, Nat.one_mul] at source
    omega
  rw [address]
  simp only [Fin.val_last]
  have shifted := time_hilbert_add index.val (blind depth index) 0
  rw [Nat.zero_add] at shifted
  exact shifted.trans (blind_coordinate depth index nonunit)

theorem blind_later_nonzero (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    phases depth index (blind depth index) (Fin.last index.val) ≠ 0 := by
  intro vanished
  have source := blind_later_coordinate depth index nonunit
  rw [vanished] at source
  exact zero_ne_one source

theorem bare_kernel_not_invariant (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    ¬ LinearMap.ker (SourceCopyGraph.recover depth index).toLinearMap ≤
      (LinearMap.ker (SourceCopyGraph.recover depth index).toLinearMap).comap SourceJointClockGraph.action.toLinearMap := by
  intro stable
  have common := SourceGeneratedActionWords.common_invariant_is_retained
    (fun _ : Unit => SourceJointClockGraph.action.toLinearMap) (SourceCopyGraph.recover depth index).toLinearMap
    (LinearMap.ker (SourceCopyGraph.recover depth index).toLinearMap) le_rfl (fun _ => stable)
  have invisible : SourceGeneratedActionWords.inventory (fun _ : Unit => SourceJointClockGraph.action.toLinearMap)
      (SourceCopyGraph.recover depth index).toLinearMap (blind depth index) = 0 := common (blind_read_zero depth index)
  have later := congrFun invisible (List.replicate index.val ())
  change SourceCopyGraph.recover depth index
    (SourceGeneratedActionWords.run (fun _ : Unit => SourceJointClockGraph.action.toLinearMap)
      (List.replicate index.val ()) (blind depth index)) = 0 at later
  rw [← time_word] at later
  apply blind_later_nonzero depth index nonunit
  rw [phase_source]
  exact later

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
