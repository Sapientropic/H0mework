import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing.Cash

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook.Cash.Origin
open ResponsibilityLifecycle
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def window (origin : Family.Origin sources) : Exposure.Window sources := ⟨origin.1,origin.2.visit⟩

def Owns {first last : ResponsibilityState (vocabulary sources)}
    (origin : Family.Origin sources) (run : (process sources).Run first last) : Prop :=
  ∀ event ∈ run.events, AssignedFinancing.Joint.Posting.eventWindow sources (sourceEvent sources event) = window sources origin

private theorem idle (origin : Family.Origin sources) (state : (process sources).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Owns sources origin (Allocation.idle sources state available nonnegative).transition := by
  intro event member
  cases member

private theorem live (origin : Family.Origin sources) (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation)
    (review : Review sources obligation.content) (selected : readReview sources obligation.content origin = some review)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Owns sources origin (allocateLive sources state index obligation present review available nonnegative).transition := by
  let cap := min available review.quantity
  have sound := live_sound sources state index obligation present
  let boundary := reviewBoundary sources obligation review cap sound.2
    (le_min nonnegative (review.quantity_nonnegative sources)) (min_le_right _ _) sound.1
  intro event member
  change event ∈ [] ++ [(NativeResponsibilityProcess.Edge.cross (P := process sources) index obligation present boundary).lifecycleEvent] at member
  simp only [List.nil_append,List.mem_singleton] at member
  subst event
  rw [cross_source sources index obligation present boundary]
  change window sources review.origin = window sources origin
  rw [Posting.selected_origin sources review selected]

theorem allocateAt (origin : Family.Origin sources) (state : (process sources).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    Owns sources origin (Family.allocateAt sources origin state position available nonnegative).transition := by
  let correct : Allocation sources state available → Prop := fun result => Owns sources origin result.transition
  change correct (Family.allocateAt sources origin state position available nonnegative)
  unfold Family.allocateAt
  split
  · split
    · exact idle sources origin state available nonnegative
    · rename_i obligation present
      split
      · exact idle sources origin state available nonnegative
      · rename_i review selected
        exact live sources origin state _ obligation present review selected available nonnegative
  · exact idle sources origin state available nonnegative

theorem allocateFrom (origin : Family.Origin sources) (fuel position : Nat) (state : (process sources).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Owns sources origin (Family.allocateFrom sources origin position fuel state available nonnegative).transition := by
  induction fuel generalizing position state available with
  | zero => exact idle sources origin state available nonnegative
  | succ fuel ih =>
      let first := Family.allocateAt sources origin state position available nonnegative
      let rest := Family.allocateFrom sources origin (position+1) fuel first.after first.remaining first.remaining_nonnegative
      intro event member
      change event ∈ (first.transition.concatRuns _ rest.transition).events at member
      rw [NativeResponsibilityProcess.Run.events_concatRuns] at member
      rcases List.mem_append.mp member with earlier | later
      · exact allocateAt sources origin state position available nonnegative event earlier
      · exact ih (position+1) first.after first.remaining first.remaining_nonnegative event later

theorem consume (origin : Family.Origin sources) (state : (process sources).GeneratedState) :
    Owns sources origin ((Family.consume sources origin state).transition sources) := by
  unfold Family.consume
  cases emitted : readIssue (sources origin.1) origin.2 with
  | issued claim exactOrigin =>
    intro event member
    change event ∈ [] ++ [NativeResponsibilityProcess.Edge.lifecycleEvent (process sources)
      (NativeResponsibilityProcess.Edge.admit ⟨origin.1,claim⟩)] at member
    simp only [List.nil_append,List.mem_singleton] at member
    subst event
    change (⟨origin.1,claim.origin.visit⟩ : Exposure.Window sources) = window sources origin
    rw [exactOrigin]
    rfl
  | rejected instruction original refused => intro event member; cases member
  | missingBirth party notBorn => intro event member; cases member
  | nonfinancial =>
    cases moved : readMovement (sources origin.1) origin.2 with
    | some movement =>
      exact allocateFrom sources origin state.current.slots.length 0 state movement.quantity (movement.quantity_nonnegative _)
    | none => intro event member; cases member

theorem record (entry : InstructionRecord sources) : Owns sources entry.origin (entry.result.transition sources) := by
  rw [entry.result_exact]
  exact consume sources entry.origin entry.before

omit [DecidableEq Port] in
private theorem inventory_visit (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (visit : LivingLawEvolution.ConstructiveRoot.RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (origin : InstructionOrigin input) (member : origin ∈ inventoryAt input visit) : origin.visit = visit := by
  cases emission : input.emission? with
  | none =>
      simp only [inventoryAt,emission,administrativeInventoryAt] at member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member; rfl
  | some emit =>
      simp only [inventoryAt,emission,List.mem_append] at member
      rcases member with administrative | traced
      · obtain ⟨index,rfl⟩ := List.mem_ofFn.mp administrative; rfl
      · obtain ⟨index,rfl⟩ := List.mem_ofFn.mp traced; rfl

theorem actual_visit (receipt : Posting.VisitReceipt sources) :
    ∀ event ∈ (receipt.native sources).events,
      AssignedFinancing.Joint.Posting.eventWindow sources (sourceEvent sources event) = receipt.window sources := by
  intro event member
  change event ∈ (consumeOrigins_run sources (visitOrigins sources receipt.sourceIndex receipt.ordinal) receipt.before).events at member
  rw [← DelayedFinancing.Cash.trace_events] at member
  obtain ⟨entry,inside,emitted⟩ := List.mem_flatMap.mp member
  have own := record sources entry event emitted
  have inOrigins : entry.origin ∈ visitOrigins sources receipt.sourceIndex receipt.ordinal := by
    rw [← DelayedFinancing.Cash.trace_origins sources (visitOrigins sources receipt.sourceIndex receipt.ordinal) receipt.before]
    exact List.mem_map.mpr ⟨entry,inside,rfl⟩
  obtain ⟨origin,inInventory,same⟩ := List.mem_map.mp inOrigins
  rw [own,← same]
  change (⟨receipt.sourceIndex,origin.visit⟩ : Exposure.Window sources) = _
  rw [inventory_visit _ _ origin inInventory]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook.Cash.Origin
