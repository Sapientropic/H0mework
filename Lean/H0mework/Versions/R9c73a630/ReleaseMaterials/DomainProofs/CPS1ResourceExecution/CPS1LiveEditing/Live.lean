import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Entry
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EndogenousTranslation.Program

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
open CPS1ResourceExecution
open CPS1Deamination CPS1Deamination.ExecutionReadout
variable {frame : CPS1Recycling.Frame}

def oldResource (species : CPS1ResourceExecution.Species) : CPS1ReactiveField.LiveMaterial frame :=
  .old (.retained (.retained (.retained (.retained (.retained (.retained (.retained (.retained
    (.retained (.retained (.old species)))))))))))

def reactiveResource (species : CPS1ResourceExecution.Species) : CPS1ReactiveField.LiveMaterial frame :=
  .reactive (.inherited (CPS1EditingChemicalJoin.Source.editingSpecies frame species))

theorem resource_origin (item : CPS1ReactiveField.LiveMaterial frame) (species : CPS1ResourceExecution.Species)
    (selected : liveResource? item = some species) :
    item = oldResource species ∨ item = reactiveResource species := by
  unfold liveResource? at selected
  split at selected <;> cases selected
  · exact Or.inl rfl
  · exact Or.inr rfl

def splitLive : List (CPS1ReactiveField.LiveMaterial frame) →
    List (CPS1ReactiveField.LiveMaterial frame) × Stock × List (CPS1ReactiveField.LiveMaterial frame)
  | [] => ([],[],[])
  | item :: rest =>
    let later := splitLive rest
    match liveResource? item with
    | none => (later.1,later.2.1,item :: later.2.2)
    | some resource => (item :: later.1,resource :: later.2.1,later.2.2)

private theorem slide (item : CPS1ReactiveField.LiveMaterial frame)
    (left right : List (CPS1ReactiveField.LiveMaterial frame)) :
    (item :: (left ++ right)).Perm (left ++ item :: right) := by
  induction left with
  | nil => exact List.Perm.rfl
  | cons first rest ih =>
    exact (List.Perm.swap _ _ _).trans (ih.cons first)

theorem split_whole (stock : List (CPS1ReactiveField.LiveMaterial frame)) :
    stock.Perm ((splitLive stock).1 ++ (splitLive stock).2.2) := by
  induction stock with
  | nil => exact List.Perm.rfl
  | cons item rest ih =>
    cases selected : liveResource? item with
    | none =>
      simpa only [splitLive,selected] using
        (ih.cons item).trans (slide item (splitLive rest).1 (splitLive rest).2.2)
    | some resource => simpa only [splitLive,selected,List.cons_append] using ih.cons item

theorem split_resources (stock : List (CPS1ReactiveField.LiveMaterial frame)) :
    (splitLive stock).2.1 = stock.filterMap liveResource? := by
  induction stock with
  | nil => rfl
  | cons item rest ih =>
    cases selected : liveResource? item <;> simp only [splitLive,selected,List.filterMap_cons,ih]

theorem live_resource_source (current : CPS1ReactiveField.Occurrence frame)
    (resource : CPS1ResourceExecution.Species) (member : resource ∈ liveResources current) :
    ∃ item ∈ CPS1ReactiveField.liveStock current,
      item = oldResource resource ∨ item = reactiveResource resource := by
  rcases List.mem_filterMap.mp member with ⟨item,held,selected⟩
  exact ⟨item,held,resource_origin item resource selected⟩

structure LiveSlice (current : CPS1ReactiveField.Occurrence frame) where
  selected : List (CPS1ReactiveField.LiveMaterial frame)
  resources : Stock
  remainder : List (CPS1ReactiveField.LiveMaterial frame)
  whole : (CPS1ReactiveField.liveStock current).Perm (selected ++ remainder)
  native : resources = liveResources current

def liveSlice (current : CPS1ReactiveField.Occurrence frame) : LiveSlice current :=
  let split := splitLive (CPS1ReactiveField.liveStock current)
  ⟨split.1,split.2.1,split.2.2,split_whole _,split_resources _⟩

def readCoding (stock : Stock) :=
  (readDNA stock).map (CodingReadout.codingFromGenomic ∘ Source.plusReadout)

def readPeptide (stock : Stock) : Option Peptide :=
  (readCoding stock).bind CPS1EndogenousTranslation.peptideFromCoding?

def readPlan (stock : Stock) : Option Program.Plan := (readPeptide stock).map Program.compile

structure ResumeEvent (current : CPS1ReactiveField.Occurrence frame) (water : Nat) where
  slice : LiveSlice current
  saved : List Reaction
  savedSource : saved = (CPS1ReactiveField.editingSource current.old).editing.remaining
  result : Execution
  actual : result = execute saved (Continuation.refillWater slice.resources water)
  dna : Option (List Base)
  dnaActual : dna = readDNA result.stock
  coding : Option SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Bases
  codingActual : coding = dna.map (CodingReadout.codingFromGenomic ∘ Source.plusReadout)
  peptide : Option Peptide
  peptideActual : peptide = coding.bind CPS1EndogenousTranslation.peptideFromCoding?
  plan : Option Program.Plan
  planActual : plan = peptide.map Program.compile

def resumeEvent (current : CPS1ReactiveField.Occurrence frame) (water : Nat) : ResumeEvent current water :=
  let slice := liveSlice current
  let saved := (CPS1ReactiveField.editingSource current.old).editing.remaining
  let result := execute saved (Continuation.refillWater slice.resources water)
  let dna := readDNA result.stock
  let coding := dna.map (CodingReadout.codingFromGenomic ∘ Source.plusReadout)
  let peptide := coding.bind CPS1EndogenousTranslation.peptideFromCoding?
  let plan := peptide.map Program.compile
  ⟨slice,saved,rfl,result,rfl,dna,rfl,coding,rfl,peptide,rfl,plan,rfl⟩

theorem resume_event_native (current : CPS1ReactiveField.Occurrence frame) (water : Nat) :
    (resumeEvent current water).result = resume current water ∧
    (CPS1ReactiveField.liveStock current).Perm
      ((resumeEvent current water).slice.selected ++ (resumeEvent current water).slice.remainder) := by
  constructor
  · unfold resumeEvent resume
    dsimp only
    rw [(liveSlice current).native]
  · exact (resumeEvent current water).slice.whole

end
end CPS1LiveEditing
