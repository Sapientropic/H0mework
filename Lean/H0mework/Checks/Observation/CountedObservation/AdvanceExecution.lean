import H0mework.Fock.SourceHistory.CountedAdvance.State

set_option autoImplicit false
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

private def entrySnapshot (entry : SourceCountedObservation.Entry) : Nat × Array ℚ × ℚ × ℚ :=
  (entry.count, entry.hilbert, entry.mass, entry.clock)

#eval do
  let eps : ℚ := 1 / 1000
  let clock := SourceConditionalNativeObservers.clockRead 0
  let parity := fun index : Nat => (index : ZMod 2)
  let keys := (List.finRange 4).map (fun actor : Fin 4 => clock actor.val)
  let data : Fin 4 → SourceRetainedReceiver.Raw 3 3 := fun actor =>
    let err : ℚ := if actor.val = 2 then -eps else eps
    (fun position => (if position.val = actor.val + 1 then 1 else 0) +
        (if position.val = 8 then err else 0),
      1 + 2 * err, (actor.val + 2 : ℚ) - 3 * err)
  let samples : {key // key ∈ keys.toFinset} → SourceRationalWindowReadout.Samples 3 4 := fun key =>
    SourceReceivedConditionalStep.completeSamples 3 3 (data ⟨(key.val.2 - 1).toNat % 4, Nat.mod_lt _ (by decide)⟩)
  let frame := SourceRetainedReceiver.start 3 3 (by decide) keys.toFinset samples
  let initial := SourceCountedObservation.fromInventory 3 3 keys frame
  let coarseFrame := SourceRetainedCoarsening.merge 3 3 frame SourceConditionalNativeMerge.forgetClock
  let coarseInitial := SourceCountedObservation.fromInventory 3 3 ([0,1] : List (ZMod 2)) coarseFrame
  let mut counts := 0
  let mut coefficients := 0
  let mut wrongReceipts := 0
  for steps in List.range 5 do
    let bound := 3 + steps
    have nonunit : bound ≠ 0 := by dsimp only [bound]; omega
    have nextNonunit : bound + 1 ≠ 0 := Nat.succ_ne_zero bound
    let table := SourceCountedObservation.run 3 (fun offset => clock (4 + offset)) initial steps
    let coarse := SourceCountedObservation.run 3 (fun offset => parity (4 + offset)) coarseInitial steps
    let fineKeys := (List.range (bound + 3)).map clock
    let coarseKeys : List (ZMod 2) := [0, 1]
    let fineBefore := fineKeys.map (fun key => entrySnapshot (SourceCountedObservation.lookup table key))
    let coarseBefore := coarseKeys.map (fun key => entrySnapshot (SourceCountedObservation.lookup coarse key))
    let advanced := SourceCountedAdvance.next bound bound nonunit table (clock (bound + 1))
    let coarseAdvanced := SourceCountedAdvance.next bound bound nonunit coarse (parity (bound + 1))
    let stepped := SourceCountedObservation.step bound table (clock (bound + 1))
    let coarseStepped := SourceCountedObservation.step bound coarse (parity (bound + 1))
    for key in fineKeys do
      let recovered := SourceCountedPosterior.restore (bound + 1) (bound + 1) nextNonunit stepped key
      let expected := SourceConditionalNativeObservers.generate clock (bound + 1) key
      unless (advanced key).1 == recovered.1 && recovered.1 == expected.1 do
        throw (IO.userError "fine autonomous next count differs from updated-table restore or original generator")
      counts := counts + 1
      for actor in List.finRange (bound + 2) do
        unless (advanced key).2 actor == recovered.2 actor && recovered.2 actor == expected.2 actor do
          throw (IO.userError "fine autonomous next posterior differs from updated-table restore or original generator")
        coefficients := coefficients + 1
    for key in coarseKeys do
      let recovered := SourceCountedPosterior.restore (bound + 1) (bound + 1) nextNonunit coarseStepped key
      let expected := SourceConditionalNativeObservers.generate parity (bound + 1) key
      unless (coarseAdvanced key).1 == recovered.1 && recovered.1 == expected.1 do
        throw (IO.userError "coarse autonomous next count differs from updated-table restore or original generator")
      counts := counts + 1
      for actor in List.finRange (bound + 2) do
        unless (coarseAdvanced key).2 actor == recovered.2 actor && recovered.2 actor == expected.2 actor do
          throw (IO.userError "coarse autonomous next posterior differs from updated-table restore or original generator")
        coefficients := coefficients + 1
    let lastActor : Fin (bound + 2) := ⟨bound + 1, Nat.lt_succ_self _⟩
    let wrongFine := SourceCountedAdvance.next bound bound nonunit table (clock (bound + 2))
    let wrongCoarse := SourceCountedAdvance.next bound bound nonunit coarse (parity (bound + 2))
    unless (wrongFine (clock (bound + 1))).1 != (advanced (clock (bound + 1))).1 &&
        (wrongFine (clock (bound + 1))).2 lastActor != (advanced (clock (bound + 1))).2 lastActor do
      throw (IO.userError "wrong fine receipt generated the actual born posterior for free")
    unless (wrongCoarse (parity (bound + 1))).1 != (coarseAdvanced (parity (bound + 1))).1 &&
        (wrongCoarse (parity (bound + 1))).2 lastActor != (coarseAdvanced (parity (bound + 1))).2 lastActor do
      throw (IO.userError "wrong coarse receipt generated the actual born posterior for free")
    wrongReceipts := wrongReceipts + 2
    unless SourceCountedObservation.coordinate (SourceCountedObservation.lookup stepped (clock 0)).hilbert 8 == eps do
      throw (IO.userError "fine future-coordinate noise was removed")
    unless SourceCountedObservation.coordinate (SourceCountedObservation.lookup coarseStepped 1).hilbert 8 -
        (if 7 ≤ bound + 1 then (1 : ℚ) else 0) == 2 * eps do
      throw (IO.userError "coarse future-coordinate noise was removed after the coordinate entered inventory")
    unless fineBefore == fineKeys.map (fun key => entrySnapshot (SourceCountedObservation.lookup table key)) &&
        coarseBefore == coarseKeys.map (fun key => entrySnapshot (SourceCountedObservation.lookup coarse key)) do
      throw (IO.userError "autonomous advance altered the original count/H/mass/clock table")
  IO.println s!"COUNTED_ADVANCE_EXECUTION=PASS prefixes=5 counts={counts} coefficients={coefficients} wrongReceipts={wrongReceipts} fineAndCoarse=complete absentAndNew=checked futureNoise=retained originalTable=unchanged"
