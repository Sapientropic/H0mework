import H0mework.Chemistry.LAlanineBandSource.Data

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSource

open SourceGaussianModel SourceSignedEvaluator SourceRectangle SourceFields
noncomputable section

def cell16Call (c : TrueTubeSource.Call) : FullBandCall := ⟨1024+c.val, by omega⟩

private def CallRestriction (c : TrueTubeSource.Call) : Prop :=
  rawCallBoxes[(cell16Call c).val]! = TrueTubeSource.rawCallBoxes[c.val]! ∧
  rawCallReductions[(cell16Call c).val]! = TrueTubeSource.rawCallReductions[c.val]! ∧
  rawCallDensity[(cell16Call c).val]! = TrueTubeWholeSource.rawCallDensity[c.val]!

private def callChunk (chunk i : Fin 8) : TrueTubeSource.Call := ⟨8*chunk.val+i.val, by omega⟩

private theorem callChunk0 : ∀ i : Fin 8, CallRestriction (callChunk 0 i) := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem callChunk1 : ∀ i : Fin 8, CallRestriction (callChunk 1 i) := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem callChunk2 : ∀ i : Fin 8, CallRestriction (callChunk 2 i) := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem callChunk3 : ∀ i : Fin 8, CallRestriction (callChunk 3 i) := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem callChunk4 : ∀ i : Fin 8, CallRestriction (callChunk 4 i) := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem callChunk5 : ∀ i : Fin 8, CallRestriction (callChunk 5 i) := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem callChunk6 : ∀ i : Fin 8, CallRestriction (callChunk 6 i) := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem callChunk7 : ∀ i : Fin 8, CallRestriction (callChunk 7 i) := by
  intro i
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem allCallChunks (chunk i : Fin 8) : CallRestriction (callChunk chunk i) := by
  fin_cases chunk
  · exact callChunk0 i
  · exact callChunk1 i
  · exact callChunk2 i
  · exact callChunk3 i
  · exact callChunk4 i
  · exact callChunk5 i
  · exact callChunk6 i
  · exact callChunk7 i

theorem cell16_raw_calls : ∀ c : TrueTubeSource.Call,
    rawCallBoxes[(cell16Call c).val]! = TrueTubeSource.rawCallBoxes[c.val]! ∧
    rawCallReductions[(cell16Call c).val]! = TrueTubeSource.rawCallReductions[c.val]! ∧
    rawCallDensity[(cell16Call c).val]! = TrueTubeWholeSource.rawCallDensity[c.val]! := by
  intro c
  let chunk : Fin 8 := ⟨c.val/8, by omega⟩
  let i : Fin 8 := ⟨c.val%8, Nat.mod_lt _ (by decide)⟩
  have address : callChunk chunk i = c := by
    apply Fin.ext
    dsimp [callChunk, chunk, i]
    omega
  have same := allCallChunks chunk i
  rw [address] at same
  exact same

theorem cell16_callBox (c : TrueTubeSource.Call) :
    callBox (cell16Call c) = TrueTubeSource.callBox c := by
  funext axis
  unfold callBox TrueTubeSource.callBox
  rw [(cell16_raw_calls c).1]

theorem cell16_callReductions (c : TrueTubeSource.Call) :
    callReductions (cell16Call c) = TrueTubeSource.callReductions c := by
  funext g
  unfold callReductions TrueTubeSource.callReductions
  rw [(cell16_raw_calls c).2.1]

theorem cell16_callReportedDensity (c : TrueTubeSource.Call) (j : LowJet) :
    callReportedDensity (cell16Call c) j = TrueTubeWholeSource.callReportedDensity c j := by
  unfold callReportedDensity TrueTubeWholeSource.callReportedDensity
  rw [(cell16_raw_calls c).2.2]

theorem cell16_recordedCallField (c : TrueTubeSource.Call) :
    recordedCallField (cell16Call c) = TrueTubeWholeSource.recordedCallField c := by
  unfold recordedCallField TrueTubeWholeSource.recordedCallField
  exact congrArg₂ IntervalParameterMap.FieldBox.mk
    (funext fun axis => cell16_callReportedDensity c _)
    (funext fun axis => funext fun direction => cell16_callReportedDensity c _)

theorem cell16_initialCallAt (d : Direction) (i : Step) :
    initialCallAt 16 d i = cell16Call (TrueTubeWholeSource.initialCallAt d i) := by
  apply Fin.ext
  dsimp [initialCallAt, callAt, rowAt, cell16Call, TrueTubeWholeSource.initialCallAt]
  omega

theorem cell16_tubeCallAt (d : Direction) (i : Step) :
    tubeCallAt 16 d i = cell16Call (TrueTubeWholeSource.tubeCallAt d i) := by
  apply Fin.ext
  dsimp [tubeCallAt, callAt, rowAt, cell16Call, TrueTubeWholeSource.tubeCallAt]
  omega

theorem cell16_raw_rows : ∀ d : Direction, ∀ i : Step,
    rawinitialBoxes[(rowAt 16 d i).val]! = TrueTubeSource.rawinitialBoxes[TrueTubeSource.rowOffset d i]! ∧
    rawtubeBoxes[(rowAt 16 d i).val]! = TrueTubeSource.rawtubeBoxes[TrueTubeSource.rowOffset d i]! ∧
    rawendpointBoxes[(rowAt 16 d i).val]! = TrueTubeSource.rawendpointBoxes[TrueTubeSource.rowOffset d i]! ∧
    rawStarts[(rowAt 16 d i).val]! = TrueTubeSource.rawStarts[TrueTubeSource.rowOffset d i]! ∧
    rawStops[(rowAt 16 d i).val]! = TrueTubeSource.rawStops[TrueTubeSource.rowOffset d i]! := by
  intro d i
  fin_cases d <;> fin_cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cell16_initialBox (d : Direction) (i : Step) : initialBox 16 d i = TrueTubeSource.initialBox d i := by
  funext axis
  unfold initialBox TrueTubeSource.initialBox
  rw [(cell16_raw_rows d i).1]

theorem cell16_tubeBox (d : Direction) (i : Step) : tubeBox 16 d i = TrueTubeSource.tubeBox d i := by
  funext axis
  unfold tubeBox TrueTubeSource.tubeBox
  rw [(cell16_raw_rows d i).2.1]

theorem cell16_endpointBox (d : Direction) (i : Step) : endpointBox 16 d i = TrueTubeSource.endpointBox d i := by
  funext axis
  unfold endpointBox TrueTubeSource.endpointBox
  rw [(cell16_raw_rows d i).2.2.1]

theorem cell16_elapsed (d : Direction) (i : Step) :
    elapsedStart 16 d i = TrueTubeSource.elapsedStart d i ∧
      elapsedStop 16 d i = TrueTubeSource.elapsedStop d i := by
  unfold elapsedStart elapsedStop TrueTubeSource.elapsedStart TrueTubeSource.elapsedStop
  rw [(cell16_raw_rows d i).2.2.2.1, (cell16_raw_rows d i).2.2.2.2]
  exact ⟨rfl, rfl⟩

theorem source_step_and_sign : stepSize = TrueTubeSource.stepSize ∧
    ∀ d : Direction, sign d = TrueTubeSource.sign d := by decide +kernel

theorem source_seed_preserved :
    initialMaxEpsilon = Geometry.Source.epsilon 0 ∧
    (∀ i : Fin 9, knotAt i = ContinuousSeed.knotCoordinate i) ∧
    (∀ i : Fin 9, lowerAt i = Geometry.Source.lower i ∧ upperAt i = Geometry.Source.upper i) := by
  decide +kernel

end
end LAlanine40K2025.BasinRefinement.WholeBandSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
