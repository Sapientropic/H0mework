import H0mework.Fock.SourceHistory.CountedObservation.Material

set_option autoImplicit false
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#eval do
  let eps : ℚ := 1 / 1000
  let clock := SourceConditionalNativeObservers.clockRead 0
  let keys := (List.finRange 4).map (fun actor : Fin 4 => clock actor.val)
  let data : Fin 4 → SourceRetainedReceiver.Raw 3 3 := fun actor =>
    let err : ℚ := if actor.val = 2 then -eps else eps
    (fun position => (if position.val = actor.val + 1 then 1 else 0) + (if position.val = 0 then err else 0),
      1 + 2 * err, (actor.val + 2 : ℚ) - 3 * err)
  let encoded : Array (Array (Array ℚ)) := (List.finRange 4).toArray.map (fun actor : Fin 4 =>
    (List.finRange 5).toArray.map (fun phase : Fin 5 =>
      (List.finRange 4).toArray.map (fun column : Fin 4 =>
        SourceReceivedConditionalStep.completeSamples 3 3 (data actor) phase column)))
  let samples : {key // key ∈ keys.toFinset} → SourceRationalWindowReadout.Samples 3 4 := fun key phase column =>
    ((encoded[(key.val.2 - 1).toNat]!)[phase.val]!)[column.val]!
  let frame := SourceRetainedReceiver.start 3 3 (by decide) keys.toFinset samples
  let initial := SourceCountedObservation.fromInventory 3 3 keys frame
  let duplicate := SourceCountedObservation.fromInventory 3 3 (keys ++ keys) frame
  unless initial.keys.length == 4 && duplicate.keys.length == 4 do
    throw (IO.userError "list inventory duplicates became new occurrences")
  let advanced := SourceCountedObservation.run 3 (fun offset => clock (4 + offset)) initial 4
  let original := SourceRetainedReceiver.run 3 3 (fun offset => clock (4 + offset)) frame 4
  unless advanced.keys.length == 8 do throw (IO.userError "actual new key was not inserted")
  for (actor : Fin 8) in List.finRange 8 do
    let key := clock actor.val
    let entry := SourceCountedObservation.lookup advanced key
    let raw := SourceCountedObservation.decode 7 7 entry
    let old := SourceRetainedReceiver.rawAt 7 7 original key
    unless entry.count == (original.native key).1 do throw (IO.userError "actual source count mismatch")
    for (position : Fin 64) in List.finRange 64 do
      unless raw.1 position == old.1 position do throw (IO.userError "full coordinate readback failed")
    unless raw.2 == old.2 do throw (IO.userError "independent mass/clock readback failed")
    if actor.val < 4 then
      let before := SourceCountedObservation.lookup initial key
      unless entry.hilbert == before.hilbert && entry.mass == before.mass && entry.clock == before.clock do
        throw (IO.userError "unselected entry was rewritten")
      unless entry.hilbert.size == 16 do throw (IO.userError "unselected array grew with the display window")
  let missing := SourceCountedObservation.lookup advanced (clock 30)
  unless missing.count == 0 && missing.hilbert.isEmpty do throw (IO.userError "missing key gained a source occurrence")
  let forget := SourceConditionalNativeMerge.forgetClock
  let coarse := SourceRetainedCoarsening.merge 7 7 original forget
  for key in ([0,1] : List (ZMod 2)) do
    let sum : SourceRetainedReceiver.Raw 7 7 := ∑ fine ∈ advanced.keys.toFinset,
      SourceCountedObservation.weight advanced forget key fine •
        SourceCountedObservation.decode 7 7 (SourceCountedObservation.lookup advanced fine)
    let raw := SourceRetainedReceiver.rawAt 7 7 coarse key
    for (position : Fin 64) in List.finRange 64 do
      unless sum.1 position == raw.1 position do throw (IO.userError "coarse observation coordinate mismatch")
    unless sum.2 == raw.2 do throw (IO.userError "coarse independent axes mismatch")
    if key == 0 then
      unless sum.1 0 == 0 && sum.2.1 == 1 do throw (IO.userError "opposite residuals did not cancel")
    else
      unless sum.1 0 == eps / 2 && sum.2.1 == 1 + eps do throw (IO.userError "same residuals were lost")
  IO.println "COUNTED_SOURCE_EXECUTION=PASS steps=4 keys=8 coordinates=640 independentAxes=kept unselectedArrays=unchanged missingKey=empty duplicateInventory=stable oppositeResidual=cancelled sameResidual=kept"
