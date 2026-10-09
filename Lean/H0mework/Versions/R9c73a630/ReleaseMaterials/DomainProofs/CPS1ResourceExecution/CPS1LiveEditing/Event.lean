import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Native

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
open CPS1ResourceExecution CPS1Deamination CPS1Deamination.ExecutionReadout
variable {frame : CPS1Recycling.Frame}

theorem refill_dna (stock : Stock) (water : Nat) :
    readDNA (Continuation.refillWater stock water) = readDNA stock := by
  simp [Continuation.refillWater,readDNA,List.filterMap_append]

structure VerifiedResume (current : CPS1ReactiveField.Occurrence frame) (water : Nat) where
  source : SavedSuffix current
  event : ResumeEvent current water
  fired : event.result.fired = (source.steps.take event.result.fired.length).map Source.Step.reaction
  remaining : event.result.remaining = (source.steps.drop event.result.fired.length).map Source.Step.reaction
  dna : event.dna = some (prefixWord source.initial (source.steps.take event.result.fired.length))
  ammonia : event.result.stock.count .ammonia = (liveResources current).count .ammonia + event.result.fired.length
  waterBalance : event.result.stock.count .water + event.result.fired.length =
    (liveResources current).count .water + water
  cut : event.result.missing = if event.result.fired.length < source.steps.length then some .water else none
  whole : (Continuation.refillWater (liveResources current) water ++ credit event.result.fired).Perm
    (event.result.stock ++ debit event.result.fired)

private def verifyResume (current : CPS1ReactiveField.Occurrence frame) (water : Nat)
    (source : SavedSuffix current) : VerifiedResume current water := by
  let event := resumeEvent current water
  let available := Continuation.refillWater (liveResources current) water
  have actual : event.result = execute (source.steps.map Source.Step.reaction) available := by
    simpa only [event,resume,source.reactions,available] using (resume_event_native current water).1
  have initial : readDNA available = some source.initial := by
    rw [refill_dna]
    exact source.actualDNA
  have generated := native_suffix_update source.initial source.final source.steps available source.follows initial
  have whole := native_execution_whole (source.steps.map Source.Step.reaction) available
  rw [← actual] at generated whole
  refine ⟨source,event,generated.1,generated.2.1,?_,?_,?_,generated.2.2.2.2.2,whole⟩
  · exact event.dnaActual.trans generated.2.2.1
  · have counted := generated.2.2.2.1
    have noAmmonia : (List.replicate water Species.water).count Species.ammonia = 0 :=
      List.count_eq_zero.mpr (by simp)
    simpa only [available,Continuation.refillWater,List.count_append,noAmmonia,Nat.add_zero] using counted
  · have counted := generated.2.2.2.2.1
    simpa [available,Continuation.refillWater] using counted

inductive GenomicDisposition (current : CPS1ReactiveField.Occurrence frame) (water : Nat)
  | rejected (slice : LiveSlice current) (available : Stock)
      (availableSource : available = Continuation.refillWater slice.resources water)
      (saved : List Reaction)
      (savedSource : saved = (CPS1ReactiveField.editingSource current.old).editing.remaining)
      (failure : SuffixFailure)
  | updated (event : VerifiedResume current water)

def genomicUpdate (current : CPS1ReactiveField.Occurrence frame) (water : Nat) : GenomicDisposition current water :=
  match savedSuffix current with
  | .error failure =>
    let slice := liveSlice current
    .rejected slice (Continuation.refillWater slice.resources water) rfl
      (CPS1ReactiveField.editingSource current.old).editing.remaining rfl failure
  | .ok source => .updated (verifyResume current water source)

theorem updated_whole (current : CPS1ReactiveField.Occurrence frame) (water : Nat) :
    match genomicUpdate current water with
    | .rejected slice _ _ _ _ _ =>
      (CPS1ReactiveField.liveStock current).Perm (slice.selected ++ slice.remainder)
    | .updated returned =>
      (CPS1ReactiveField.liveStock current).Perm (returned.event.slice.selected ++ returned.event.slice.remainder) ∧
      returned.event.coding = returned.event.dna.map (CodingReadout.codingFromGenomic ∘ Source.plusReadout) ∧
      returned.event.peptide = returned.event.coding.bind CPS1EndogenousTranslation.peptideFromCoding? ∧
      returned.event.plan = returned.event.peptide.map Program.compile := by
  unfold genomicUpdate
  cases savedSuffix current with
  | error failure => exact (liveSlice current).whole
  | ok source =>
    exact ⟨(verifyResume current water source).event.slice.whole,(verifyResume current water source).event.codingActual,
      (verifyResume current water source).event.peptideActual,(verifyResume current water source).event.planActual⟩

end
end CPS1LiveEditing
