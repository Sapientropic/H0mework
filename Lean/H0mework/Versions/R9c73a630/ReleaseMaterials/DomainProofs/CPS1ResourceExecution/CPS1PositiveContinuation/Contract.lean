import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositiveContinuation.NativeSource

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositiveContinuation
noncomputable section

structure PositiveContinuationContract : Prop where
  strictNeighborhood : type_of% @CPS1PositiveContinuation.pulse_eventually_ready
  renewingExistence : type_of% @CPS1PositiveContinuation.exists_renewing_dyadic
  renewedIndex : type_of% @CPS1PositiveContinuation.renewing_index_spec
  renewedMinimum : type_of% @CPS1PositiveContinuation.renewing_index_minimal
  renewedActual : type_of% @CPS1PositiveContinuation.renewing_actual
  renewedReady : type_of% @CPS1PositiveContinuation.renewing_ready
  renewedPositiveTime : type_of% @CPS1PositiveContinuation.renewing_time_positive
  renewedPayment : type_of% @CPS1PositiveContinuation.renewing_paid
  trajectoryActual : type_of% @CPS1PositiveContinuation.trajectory_actual
  trajectoryReady : type_of% @CPS1PositiveContinuation.trajectory_ready
  trajectoryPositiveTime : type_of% @CPS1PositiveContinuation.trajectory_positive_time
  trajectoryPayment : type_of% @CPS1PositiveContinuation.trajectory_paid
  trajectorySource : type_of% @CPS1PositiveContinuation.trajectory_same_source
  elapsedProgress : type_of% @CPS1PositiveContinuation.elapsed_strict
  elapsedPositive : type_of% @CPS1PositiveContinuation.elapsed_positive
  rawProgramSize : type_of% @CPS1PositiveContinuation.NativeSource.raw_block_length
  physicalProgramSize : type_of% @CPS1PositiveContinuation.NativeSource.reaction_block_length
  actualProgram : type_of% @CPS1PositiveContinuation.NativeSource.program_block
  availableCarrier : type_of% @CPS1PositiveContinuation.NativeSource.available_held
  fullPrefix : type_of% @CPS1PositiveContinuation.NativeSource.prefix_paid
  nativeProgram : type_of% @CPS1PositiveContinuation.NativeSource.generated_program
  fullExecution : type_of% @CPS1PositiveContinuation.NativeSource.fired_prefix_and_suffix
  nativeExecution : type_of% @CPS1PositiveContinuation.NativeSource.continued_execution
  finalStock : type_of% @CPS1PositiveContinuation.NativeSource.continued_final_stock
  actualPending : type_of% @CPS1PositiveContinuation.NativeSource.continued_pending
  samePrevious : type_of% @CPS1PositiveContinuation.NativeSource.continued_previous
  wholeInventory : type_of% @CPS1PositiveContinuation.NativeSource.continued_whole_inventory
  actualCut : type_of% @CPS1PositiveContinuation.NativeSource.continued_cut
  terminalReady : type_of% @CPS1PositiveContinuation.NativeSource.terminal_ready
  terminalPayment : type_of% @CPS1PositiveContinuation.NativeSource.terminal_payment
  terminalSource : type_of% @CPS1PositiveContinuation.NativeSource.terminal_source
  positiveTime : type_of% @CPS1PositiveContinuation.NativeSource.generated_time_positive
  goodStock : type_of% @CPS1PositiveContinuation.NativeSource.continued_stock_good
  noGuardStock : type_of% @CPS1PositiveContinuation.NativeSource.continued_stock_noGuard
  publicEmitter : type_of% @CPS1PositiveContinuation.NativeSource.auto_continue_generated
  nativeNext : type_of% @CPS1PositiveContinuation.NativeSource.next_previous

theorem sourceGeneratedPositiveContinuation : PositiveContinuationContract :=
  ⟨@CPS1PositiveContinuation.pulse_eventually_ready,
   @CPS1PositiveContinuation.exists_renewing_dyadic,
   @CPS1PositiveContinuation.renewing_index_spec,
   @CPS1PositiveContinuation.renewing_index_minimal,
   @CPS1PositiveContinuation.renewing_actual,
   @CPS1PositiveContinuation.renewing_ready,
   @CPS1PositiveContinuation.renewing_time_positive,
   @CPS1PositiveContinuation.renewing_paid,
   @CPS1PositiveContinuation.trajectory_actual,
   @CPS1PositiveContinuation.trajectory_ready,
   @CPS1PositiveContinuation.trajectory_positive_time,
   @CPS1PositiveContinuation.trajectory_paid,
   @CPS1PositiveContinuation.trajectory_same_source,
   @CPS1PositiveContinuation.elapsed_strict,
   @CPS1PositiveContinuation.elapsed_positive,
   @CPS1PositiveContinuation.NativeSource.raw_block_length,
   @CPS1PositiveContinuation.NativeSource.reaction_block_length,
   @CPS1PositiveContinuation.NativeSource.program_block,
   @CPS1PositiveContinuation.NativeSource.available_held,
   @CPS1PositiveContinuation.NativeSource.prefix_paid,
   @CPS1PositiveContinuation.NativeSource.generated_program,
   @CPS1PositiveContinuation.NativeSource.fired_prefix_and_suffix,
   @CPS1PositiveContinuation.NativeSource.continued_execution,
   @CPS1PositiveContinuation.NativeSource.continued_final_stock,
   @CPS1PositiveContinuation.NativeSource.continued_pending,
   @CPS1PositiveContinuation.NativeSource.continued_previous,
   @CPS1PositiveContinuation.NativeSource.continued_whole_inventory,
   @CPS1PositiveContinuation.NativeSource.continued_cut,
   @CPS1PositiveContinuation.NativeSource.terminal_ready,
   @CPS1PositiveContinuation.NativeSource.terminal_payment,
   @CPS1PositiveContinuation.NativeSource.terminal_source,
   @CPS1PositiveContinuation.NativeSource.generated_time_positive,
   @CPS1PositiveContinuation.NativeSource.continued_stock_good,
   @CPS1PositiveContinuation.NativeSource.continued_stock_noGuard,
   @CPS1PositiveContinuation.NativeSource.auto_continue_generated,
   @CPS1PositiveContinuation.NativeSource.next_previous⟩

end
end CPS1PositiveContinuation
