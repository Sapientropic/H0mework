import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Genome
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Programme

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1Deamination CPS1Deamination.ExecutionReadout

def translationRawForTail (tail : List AA) : List RawSupply :=
  [.aminoAcid .M,.initiatorTrna,.atp] ++
    tail.flatMap (fun aa => [.aminoAcid aa,.trna aa,.atp]) ++
    [.subunit40,.subunit60] ++
    ([.metRS,.eIF1,.eIF1A,.eIF2,.eIF3,.eIF5,.eIF5B,.eRF1,.eRF3].map RawSupply.actor) ++
    [.gtp,.water,.gtp,.water] ++ tail.flatMap (fun _ => [.gtp,.water,.gtp,.water]) ++
    [.gtp,.water,.water]

theorem translation_raw_species (tail : List AA) :
    (translationRawForTail tail).map RawSupply.species = CPS1InitiationTermination.NativeComplete.rawFuel tail := by
  simp [translationRawForTail,RawSupply.species,CPS1InitiationTermination.NativeComplete.rawFuel,
    CPS1EndogenousTranslation.chargingFuel,CPS1InitiationTermination.NativeComplete.actors,
    CPS1InitiationTermination.NativeComplete.energyFuel,factorStock,List.map_flatMap,Reaction.reactants]

noncomputable def registeredTranslationRaw : List RawSupply :=
  translationRawForTail CPS1EndogenousTranslation.correctedPeptide.2

noncomputable def registeredSupply : ContinuationRaw :=
  ⟨0,registeredTranslationRaw,.first,[],[],noPhysicalSupply,0⟩

attribute [local irreducible] registeredBefore registeredOld

theorem registered_before_dna :
    readDNA (liveResources registeredBefore.native.current) = some registeredDNA :=
  registered_before_genome.trans (congrArg List.head? registered_old_genome)

theorem registered_before_remaining :
    (CPS1ReactiveField.editingSource registeredBefore.native.current.old).editing.remaining =
      ((CPS1Deamination.Source.sourceProgram registeredEdits).steps.drop 1).map CPS1Deamination.Source.Step.reaction := by
  have source := congrArg Execution.remaining registered_before_editing
  have remaining := (CPS1Deamination.Continuation.source_continuation_update
    registeredEdits registeredWater registeredAdditional).2.1
  exact source.trans remaining

private theorem verified_resume_complete {frame : CPS1Recycling.Frame}
    {current : CPS1ReactiveField.Occurrence frame} {water : Nat}
    (event : VerifiedResume current water) (enough : event.source.steps.length ≤ water) :
    event.event.result.fired.length = event.source.steps.length ∧ event.event.result.remaining = [] ∧
      event.event.dna = some (prefixWord event.source.initial event.source.steps) := by
  have actual : event.event.result = execute (event.source.steps.map CPS1Deamination.Source.Step.reaction)
      (Continuation.refillWater (liveResources current) water) := by
    rw [event.event.actual,event.event.savedSource,← event.source.reactions,event.event.slice.native]
  have bound := congrArg List.length event.fired
  simp only [List.length_map,List.length_take] at bound
  have upper : event.event.result.fired.length ≤ event.source.steps.length := by omega
  have equal : event.event.result.fired.length = event.source.steps.length := by
    by_contra different
    have short : event.event.result.fired.length < event.source.steps.length := by omega
    have missing : event.event.result.missing = some .water := by rw [event.cut,if_pos short]
    have actualCut := missing
    rw [actual] at actualCut
    obtain ⟨reaction,rest,pending,shortage⟩ := CPS1ResourceExecution.execution_cut _ _ .water actualCut
    rw [← actual] at pending shortage
    have member : reaction ∈ event.event.result.remaining := by rw [pending]; exact List.mem_cons_self
    rw [event.remaining] at member
    obtain ⟨step,_held,same⟩ := List.mem_map.mp member
    subst reaction
    have price : (CPS1Deamination.Source.Step.reaction step).reactants.count .water = 1 := by
      simp [CPS1Deamination.Source.Step.reaction,Reaction.reactants]
    rw [price] at shortage
    have balance := event.waterBalance
    omega
  refine ⟨equal,?_,?_⟩
  · rw [event.remaining,equal,List.drop_length,List.map_nil]
  · simpa only [equal,List.take_length] using event.dna

private def reactionOutput : Reaction → List Base
  | .deaminate left right => left ++ .I :: right
  | _ => []

private theorem prefix_from_reactions (initial : List Base) (steps : List CPS1Deamination.Source.Step) :
    prefixWord initial steps =
      (steps.map CPS1Deamination.Source.Step.reaction).foldl (fun _ reaction => reactionOutput reaction) initial := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step rest ih =>
    simpa only [prefixWord,List.foldl_cons,List.map_cons,CPS1Deamination.Source.Step.reaction,reactionOutput,
      CPS1Deamination.Source.Step.output] using ih step.output

private theorem saved_suffix_from_registered {frame : CPS1Recycling.Frame}
    (current : CPS1ReactiveField.Occurrence frame)
    (dna : readDNA (liveResources current) = some registeredDNA)
    (remaining : (CPS1ReactiveField.editingSource current.old).editing.remaining =
      ((CPS1Deamination.Source.sourceProgram registeredEdits).steps.drop 1).map CPS1Deamination.Source.Step.reaction) :
    ∃ suffix, savedSuffix current = .ok suffix := by
  unfold savedSuffix
  split
  · rename_i absent
    rw [dna] at absent
    cases absent
  · rename_i initial found
    have same : initial = registeredDNA := Option.some.inj (found.symm.trans dna)
    subst initial
    split
    · rename_i failure cut
      rw [remaining] at cut
      cases cut
    · exact ⟨_,rfl⟩

private theorem suffix_from_registered_complete {frame : CPS1Recycling.Frame}
    {current : CPS1ReactiveField.Occurrence frame}
    (dna : readDNA (liveResources current) = some registeredDNA)
    (remaining : (CPS1ReactiveField.editingSource current.old).editing.remaining =
      ((CPS1Deamination.Source.sourceProgram registeredEdits).steps.drop 1).map CPS1Deamination.Source.Step.reaction)
    (suffix : SavedSuffix current) :
    suffix.steps.length = 2 ∧
      prefixWord suffix.initial suffix.steps = (CPS1Deamination.Source.sourceProgram registeredEdits).word := by
  have initial : suffix.initial = registeredDNA :=
    Option.some.inj (suffix.actualDNA.symm.trans dna)
  have reactions := suffix.reactions.trans remaining
  have length := congrArg List.length reactions
  simp only [List.length_map] at length
  have count : ((CPS1Deamination.Source.sourceProgram registeredEdits).steps.drop 1).length = 2 := by
    decide +kernel
  refine ⟨length.trans count,?_⟩
  rw [prefix_from_reactions,reactions,initial]
  decide +kernel

private theorem verified_from_registered_complete {frame : CPS1Recycling.Frame}
    {current : CPS1ReactiveField.Occurrence frame}
    (dnaSource : readDNA (liveResources current) = some registeredDNA)
    (remaining : (CPS1ReactiveField.editingSource current.old).editing.remaining =
      ((CPS1Deamination.Source.sourceProgram registeredEdits).steps.drop 1).map CPS1Deamination.Source.Step.reaction)
    (event : VerifiedResume current 2) :
    event.event.result.fired.length = 2 ∧ event.event.result.remaining = [] ∧
      event.event.dna = some (CPS1Deamination.Source.sourceProgram registeredEdits).word ∧
      event.event.peptide = some CPS1EndogenousTranslation.correctedPeptide ∧
      0 < event.event.result.stock.count .ammonia := by
  have shape := suffix_from_registered_complete dnaSource remaining event.source
  have complete := verified_resume_complete event (by omega)
  have dna : event.event.dna = some (CPS1Deamination.Source.sourceProgram registeredEdits).word :=
    complete.2.2.trans (congrArg some shape.2)
  have peptide : event.event.peptide = some CPS1EndogenousTranslation.correctedPeptide := by
    rw [event.event.peptideActual,event.event.codingActual,dna]
    decide +kernel
  have ammonia := event.ammonia
  exact ⟨complete.1.trans shape.1,complete.2.1,dna,peptide,by omega⟩

private theorem genomic_from_registered_complete {frame : CPS1Recycling.Frame}
    (current : CPS1ReactiveField.Occurrence frame)
    (dna : readDNA (liveResources current) = some registeredDNA)
    (remaining : (CPS1ReactiveField.editingSource current.old).editing.remaining =
      ((CPS1Deamination.Source.sourceProgram registeredEdits).steps.drop 1).map CPS1Deamination.Source.Step.reaction) :
    match genomicUpdate current 2 with
    | .rejected _ _ _ _ _ _ => False
    | .updated event => event.event.result.fired.length = 2 ∧
        event.event.result.remaining = [] ∧
        event.event.dna = some (CPS1Deamination.Source.sourceProgram registeredEdits).word ∧
        event.event.peptide = some CPS1EndogenousTranslation.correctedPeptide ∧
        0 < event.event.result.stock.count .ammonia := by
  obtain ⟨suffix,selected⟩ := saved_suffix_from_registered current dna remaining
  have generated : ∃ event, genomicUpdate current 2 = .updated event := by
    unfold genomicUpdate
    rw [selected]
    exact ⟨_,rfl⟩
  obtain ⟨event,actual⟩ := generated
  rw [actual]
  exact verified_from_registered_complete dna remaining event

theorem registered_genomic_complete :
    type_of% (genomic_from_registered_complete registeredBefore.native.current registered_before_dna registered_before_remaining) :=
  genomic_from_registered_complete registeredBefore.native.current registered_before_dna registered_before_remaining

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
