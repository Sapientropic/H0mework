import H0mework.Fock.SourceHistory.CountedPosterior.Restore

set_option autoImplicit false
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#eval do
  let eps : ℚ := 1 / 1000
  let clock := SourceConditionalNativeObservers.clockRead 0
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
  let mut checked := 0
  for steps in List.range 5 do
    let bound := 3 + steps
    have nonunit : bound ≠ 0 := by dsimp only [bound]; omega
    let table := SourceCountedObservation.run 3 (fun offset => clock (4 + offset)) initial steps
    let coarse := SourceCountedObservation.run 3 (fun offset => ((4 + offset : Nat) : ZMod 2)) coarseInitial steps
    for key in (List.range (bound + 2)).map clock do
      let recovered := SourceCountedPosterior.restore bound bound nonunit table key
      let expected := SourceConditionalNativeObservers.generate clock bound key
      unless recovered.1 == expected.1 do throw (IO.userError "fine count recovery failed")
      for actor in List.finRange (bound + 1) do
        unless recovered.2 actor == expected.2 actor do throw (IO.userError "complete fine posterior recovery failed")
        checked := checked + 1
    for key in ([0,1] : List (ZMod 2)) do
      let recovered := SourceCountedPosterior.restore bound bound nonunit coarse key
      let expected := SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) bound key
      unless recovered.1 == expected.1 do throw (IO.userError "coarse count recovery failed")
      for actor in List.finRange (bound + 1) do
        unless recovered.2 actor == expected.2 actor do throw (IO.userError "complete coarse posterior recovery failed")
        checked := checked + 1
    unless (SourceCountedObservation.lookup table (clock 0)).hilbert ==
        (SourceCountedObservation.lookup initial (clock 0)).hilbert do
      throw (IO.userError "posterior recovery modified the original noisy observation")
  let boundary : SourceCountedObservation.Entry := ⟨1, #[0, 1 / 2], 1, 2⟩
  let boundaryTable : SourceCountedObservation.Table Nat := SourceCountedObservation.collect [0] (fun _ => boundary)
  let boundaryRead := SourceCountedPosterior.restore 3 3 (by decide) boundaryTable 0
  unless boundaryRead.1 == 0 do throw (IO.userError "half-margin boundary was treated as a certified positive signal")
  IO.println s!"COUNTED_POSTERIOR_EXECUTION=PASS trajectories=5 coefficients={checked} fineAndCoarse=complete futureCoordinate=kept absent=zero rawNoise=retained halfBoundary=excluded"
