import H0mework.Fock.SourceHistory.CountedObservation.Material

set_option autoImplicit false
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

-- The finite coordinates include both independent axes and every nonzero H coordinate in this fixture.
private def sourceAxis (actor axis : Nat) : ℚ :=
  if axis = 0 then 1 else if axis = 1 then actor + 2 else if axis = actor + 3 then 1 else 0

private def observedAxis (table : SourceCountedObservation.Table (ℤ × ℤ))
    (coarse : ZMod 2) (axis : Nat) : ℚ :=
  ∑ key ∈ table.keys.toFinset,
    let entry := SourceCountedObservation.lookup table key
    SourceCountedObservation.weight table SourceConditionalNativeMerge.forgetClock coarse key *
      (if axis = 0 then entry.mass / entry.count else if axis = 1 then entry.clock / entry.count
        else SourceCountedObservation.coordinate entry.hilbert (axis - 2) / entry.count)

private def squareError (left right : Nat → ℚ) : ℚ :=
  ((List.range 66).map (fun axis => (left axis - right axis) ^ 2)).sum

private def physicalError (bound : Nat) (table : SourceCountedObservation.Table (ℤ × ℤ)) : ℚ :=
  ((List.range (bound + 1)).map (fun actor =>
    squareError (sourceAxis actor) (observedAxis table (actor : ZMod 2)))).sum

#eval do
  let eps : ℚ := 1 / 1000
  let clock := SourceConditionalNativeObservers.clockRead 0
  let keys := (List.finRange 4).map (fun actor : Fin 4 => clock actor.val)
  let data : Fin 4 → SourceRetainedReceiver.Raw 3 3 := fun actor =>
    let err : ℚ := if actor.val = 2 then -eps else eps
    (fun position => (if position.val = actor.val + 1 then 1 else 0) + (if position.val = 0 then err else 0),
      1 + 2 * err, (actor.val + 2 : ℚ) - 3 * err)
  let samples : {key // key ∈ keys.toFinset} → SourceRationalWindowReadout.Samples 3 4 := fun key =>
    SourceReceivedConditionalStep.completeSamples 3 3 (data ⟨(key.val.2 - 1).toNat % 4, Nat.mod_lt _ (by decide)⟩)
  let frame := SourceRetainedReceiver.start 3 3 (by decide) keys.toFinset samples
  let mut table := SourceCountedObservation.fromInventory 3 3 keys frame
  let mut positiveRecovery := 0
  let mut cancelledRecovery := 0
  for offset in List.range 4 do
    let bound := 3 + offset
    let coarse : ZMod 2 := (bound + 1 : Nat)
    let actors : List Nat := (List.range (bound + 1)).filter (fun actor : Nat => (actor : ZMod 2) == coarse)
    let count := SourceCountedObservation.total table SourceConditionalNativeMerge.forgetClock coarse
    unless count == actors.length do throw (IO.userError "coarse count differs from actual source inventory")
    let mean : Nat → ℚ := fun axis => ((actors.map (fun actor => sourceAxis actor axis)).sum) / count
    let ratio : ℚ := (count : ℚ) / (count + 1 : Nat)
    let innovation := ratio * squareError (sourceAxis (bound + 1)) mean
    let recovery := ratio * squareError (observedAxis table coarse) mean
    let advanced := SourceCountedObservation.step bound table (clock (bound + 1))
    let before := physicalError bound table
    let after := physicalError (bound + 1) advanced
    unless after == before + innovation - recovery do throw (IO.userError "actual Field increment lost innovation or residual recovery")
    if coarse == 0 then
      unless recovery == 0 do throw (IO.userError "opposite residuals acquired a fictitious recovery gain")
      cancelledRecovery := cancelledRecovery + 1
    else
      unless recovery > 0 && after != before + innovation do throw (IO.userError "same residual recovery was omitted")
      positiveRecovery := positiveRecovery + 1
    unless after > before do throw (IO.userError "source innovation was replaced by unconditional total-error decrease")
    table := advanced
  IO.println s!"COUNTED_RECOVERY_EXECUTION=PASS receipts=4 coarseCounts=actual fullAxes=66 positiveRecovery={positiveRecovery} cancelledRecovery={cancelledRecovery} sourceInnovation=retained"
