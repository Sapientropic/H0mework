import H0mework.Fock.SourceHistory.CountedMerge.Table
import H0mework.Fock.SourceHistory.CountedPosterior.Restore

set_option autoImplicit false
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

private def checkEntry (left right : SourceCountedObservation.Entry) (positions : Nat)
    (label : String) : IO Nat := do
  unless left.count == right.count && left.mass == right.mass && left.clock == right.clock do
    throw (IO.userError s!"{label}: count/mass/clock differs")
  for position in List.range positions do
    unless SourceCountedObservation.coordinate left.hilbert position ==
        SourceCountedObservation.coordinate right.hilbert position do
      throw (IO.userError s!"{label}: H coordinate {position} differs")
  return positions

private def checkPosterior (bound : Nat) (nonunit : bound ≠ 0)
    (table : SourceCountedObservation.Table Nat) (read : Nat → Nat) (key : Nat) : IO Nat := do
  let recovered := SourceCountedPosterior.restore bound bound nonunit table key
  let expected := SourceConditionalNativeObservers.generate read bound key
  unless recovered.1 == expected.1 do throw (IO.userError "merged posterior count differs")
  for actor in List.finRange (bound + 1) do
    unless recovered.2 actor == expected.2 actor do
      throw (IO.userError "merged complete posterior differs")
  return bound + 1

#eval do
  let eps : ℚ := 1 / 1000
  let read := fun index : Nat => index % 3
  let forget := fun key : Nat => key % 2
  let keys : List Nat := [0, 1, 2, 3]
  let data : Nat → SourceRetainedReceiver.Raw 3 3 := fun key =>
    let count := ((List.range 4).filter (fun actor => read actor == key)).length
    let err : ℚ := if key = 0 then eps else if key = 1 then -eps else 3 * eps
    if count = 0 then (fun _ => 0, 0, 0) else
      (fun position =>
        (if 0 < position.val ∧ position.val ≤ 4 ∧ read (position.val - 1) = key then (count : ℚ)⁻¹ else 0) +
          (if position.val = 8 then err else 0),
        1 + 2 * err,
        ((List.range 4).foldl (fun total actor =>
          if read actor = key then total + (actor + 2 : ℚ) else total) 0) / count - 3 * err)
  let samples : {key // key ∈ keys.toFinset} → SourceRationalWindowReadout.Samples 3 4 := fun key =>
    SourceReceivedConditionalStep.completeSamples 3 3 (data key.val)
  let frame := SourceRetainedReceiver.start 3 3 (by decide) keys.toFinset samples
  let initial := SourceCountedObservation.fromInventory 3 3 keys frame
  let initialSnapshot := keys.map (fun key =>
    let entry := SourceCountedObservation.lookup initial key
    (entry.count, entry.hilbert, entry.mass, entry.clock))
  let mut coordinates := 0
  let mut coefficients := 0
  let mut weightedControls := 0
  for steps in List.range 5 do
    let bound := 3 + steps
    have nonunit : bound ≠ 0 := by dsimp only [bound]; omega
    have nextNonunit : bound + 1 ≠ 0 := Nat.succ_ne_zero bound
    let table := SourceCountedObservation.run 3 (fun offset => read (4 + offset)) initial steps
    let retained := SourceRetainedReceiver.run 3 3 (fun offset => read (4 + offset)) frame steps
    let merged := SourceCountedMerge.mergeTable table forget
    let originalMerged := SourceRetainedCoarsening.merge bound bound retained forget
    let oracle := SourceCountedObservation.fromInventory bound bound [0, 1] originalMerged
    let receipt := read (bound + 1)
    let mergeThenStep := SourceCountedObservation.step bound merged (forget receipt)
    let stepThenMerge := SourceCountedMerge.mergeTable (SourceCountedObservation.step bound table receipt) forget
    let nextRetained := SourceRetainedReceiver.step bound bound (bound + 1) retained receipt
    let nextOriginalMerged := SourceRetainedCoarsening.merge (bound + 1) (bound + 1) nextRetained forget
    let nextOracle := SourceCountedObservation.fromInventory (bound + 1) (bound + 1) [0, 1] nextOriginalMerged
    for key in [0, 1, 2, 3] do
      coordinates := coordinates + (← checkEntry (SourceCountedObservation.lookup merged key)
        (SourceCountedObservation.lookup oracle key) ((bound + 1) ^ 2 + 5) "original merged Frame")
      coordinates := coordinates + (← checkEntry (SourceCountedObservation.lookup mergeThenStep key)
        (SourceCountedObservation.lookup stepThenMerge key) ((bound + 2) ^ 2 + 5) "receipt/merge square")
      coordinates := coordinates + (← checkEntry (SourceCountedObservation.lookup stepThenMerge key)
        (SourceCountedObservation.lookup nextOracle key) ((bound + 2) ^ 2 + 5) "next original merged Frame")
      coefficients := coefficients + (← checkPosterior bound nonunit merged (forget ∘ read) key)
      coefficients := coefficients + (← checkPosterior (bound + 1) nextNonunit stepThenMerge (forget ∘ read) key)
    let fine0 := SourceCountedObservation.lookup table 0
    let fine2 := SourceCountedObservation.lookup table 2
    if fine0.count != fine2.count then
      let actual := SourceCountedObservation.coordinate (SourceCountedObservation.lookup merged 0).hilbert 1 /
        (SourceCountedObservation.lookup merged 0).count
      let unweighted := (SourceCountedObservation.coordinate fine0.hilbert 1 / fine0.count +
        SourceCountedObservation.coordinate fine2.hilbert 1 / fine2.count) / 2
      unless actual != unweighted do throw (IO.userError "unweighted cell average replaced actual count weights")
      weightedControls := weightedControls + 1
    let zeroRow := SourceCountedObservation.lookup stepThenMerge 0
    unless SourceCountedObservation.coordinate zeroRow.hilbert 8 == 5 * eps &&
        zeroRow.mass - zeroRow.count == 10 * eps do
      throw (IO.userError "merge removed the original independent H/mass noise")
    let oneRow := SourceCountedObservation.lookup stepThenMerge 1
    unless SourceCountedObservation.coordinate oneRow.hilbert 8 -
        (if 7 ≤ bound + 1 then (1 : ℚ) else 0) == -eps do
      throw (IO.userError "future-coordinate noise disappeared when its coordinate entered inventory")
  let zeroOnly := SourceCountedObservation.collect [3] (fun _ => SourceCountedObservation.emptyEntry)
  let mergedZero := SourceCountedMerge.mergeTable zeroOnly forget
  coordinates := coordinates + (← checkEntry (SourceCountedObservation.lookup mergedZero 1)
    SourceCountedObservation.emptyEntry 20 "present zero-count cell")
  let recoveredZero := SourceCountedPosterior.restore 3 3 (by decide) mergedZero 1
  unless recoveredZero.1 == 0 do throw (IO.userError "zero-count merged cell generated positive support")
  for actor in List.finRange 4 do
    unless recoveredZero.2 actor == 0 do throw (IO.userError "zero-count merged cell generated a posterior")
  unless initialSnapshot == keys.map (fun key =>
      let entry := SourceCountedObservation.lookup initial key
      (entry.count, entry.hilbert, entry.mass, entry.clock)) do
    throw (IO.userError "merge modified the original fine table")
  IO.println s!"COUNTED_MERGE_EXECUTION=PASS prefixes=5 coordinates={coordinates} posteriorCoefficients={coefficients} unequalWeightControls={weightedControls} receiptSquare=checked originalFrame=checked absentAndZero=checked noise=retained sourceTable=unchanged"
