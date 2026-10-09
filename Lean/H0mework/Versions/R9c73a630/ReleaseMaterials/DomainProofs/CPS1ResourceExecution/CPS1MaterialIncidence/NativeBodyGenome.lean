import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativeAdoptedNext
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Live

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeBodyGenomeProbe
noncomputable section
open CPS1ResourceExecution CPS1SameEventFunction CPS1PhosphorylExchange CPS1LiveEditing
open CPS1Deamination.ExecutionReadout
open NativePaidEvent NativeCPContinuationProbe NativePrepareNextProbe NativePrepareBinding NativeAdoptionProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}

private theorem owned_resource_none (item : CPS1ReactiveField.LiveMaterial frame)
    (owner : Classical.OwnedChain frame) (actual : Classical.ownedLive? item = some owner) :
    liveResource? item = none := by
  cases selected : liveResource? item with
  | none => rfl
  | some resource =>
    rcases resource_origin item resource selected with old | reactive
    · rw [old] at actual
      change (none : Option (Classical.OwnedChain frame)) = some owner at actual
      cases actual
    · rw [reactive] at actual
      change (none : Option (Classical.OwnedChain frame)) = some owner at actual
      cases actual

theorem chain_resource_absent (current : NativeCurrent source) :
    liveResource? ((LiveStock cursor).get current.chainSlot) = none :=
  owned_resource_none _ _ current.chainSlotActual

private theorem ammonia_resource (item : CPS1ReactiveField.LiveMaterial frame)
    (actual : CPS1BiologicalUpdate.liveLocal? item = some (CPS1LocalChemicalExecution.molecule frame .ammonia)) :
    liveResource? item = some CPS1ResourceExecution.Species.ammonia := by
  unfold CPS1BiologicalUpdate.liveLocal? at actual
  split at actual <;> cases actual <;> rfl

theorem ammonia_resource_actual (original : Classical.Source cursor) :
    liveResource? ((LiveStock cursor).get original.ammonia.slot) = some CPS1ResourceExecution.Species.ammonia :=
  ammonia_resource _ original.ammonia.species

private def dnaWord? : CPS1ResourceExecution.Species → Option (List CPS1Deamination.Base)
  | .dna word => some word
  | _ => none

private def liveDNA? (item : CPS1ReactiveField.LiveMaterial frame) :=
  (liveResource? item).bind dnaWord?

private theorem filterMap_ignored {α β γ : Type} (entries : List α) (skip : α → Prop)
    [DecidablePred skip] (value : α → β) (decode : β → Option γ)
    (ignored : ∀ entry ∈ entries, skip entry → decode (value entry) = none) :
    (entries.filterMap (fun entry => if skip entry then none else some (value entry))).filterMap decode =
      entries.filterMap (fun entry => decode (value entry)) := by
  revert ignored
  induction entries with
  | nil => intro _; rfl
  | cons entry rest ih =>
    intro ignored
    have later : ∀ item ∈ rest, skip item → decode (value item) = none :=
      fun item held => ignored item (List.mem_cons_of_mem _ held)
    by_cases paid : skip entry
    · have absent := ignored entry (List.mem_cons_self ..) paid
      simp only [List.filterMap_cons,if_pos paid,absent,ih later]
    · cases selected : decode (value entry) <;>
        simp only [List.filterMap_cons,if_neg paid,selected,ih later]

private theorem remaining_dna_words (current : NativeCurrent source) :
    (current.remaining.filterMap liveResource?).filterMap dnaWord? =
      ((LiveStock cursor).filterMap liveResource?).filterMap dnaWord? := by
  have erased : current.remaining.filterMap liveDNA? = (LiveStock cursor).filterMap liveDNA? := by
    rw [current.remainingActual]
    unfold unspentLive
    calc
      _ = (LiveStock cursor).zipIdx.filterMap (fun entry => liveDNA? entry.1) := by
        apply filterMap_ignored
        rintro ⟨item,slot⟩ held (chain | ammonia)
        · change slot = current.chainSlot.val at chain
          change liveDNA? item = none
          have found : (LiveStock cursor)[slot]? = some item := List.mk_mem_zipIdx_iff_getElem?.mp held
          rw [chain] at found
          have selected : (LiveStock cursor)[current.chainSlot.val]? =
              some ((LiveStock cursor).get current.chainSlot) :=
            List.getElem?_eq_some_iff.mpr ⟨current.chainSlot.isLt,rfl⟩
          have same := Option.some.inj (found.symm.trans selected)
          rw [same,liveDNA?,chain_resource_absent current]
          rfl
        · change slot = before.packet.source.ammonia.slot.val at ammonia
          change liveDNA? item = none
          have found : (LiveStock cursor)[slot]? = some item := List.mk_mem_zipIdx_iff_getElem?.mp held
          rw [ammonia] at found
          have selected : (LiveStock cursor)[before.packet.source.ammonia.slot.val]? =
              some ((LiveStock cursor).get before.packet.source.ammonia.slot) :=
            List.getElem?_eq_some_iff.mpr ⟨before.packet.source.ammonia.slot.isLt,rfl⟩
          have same := Option.some.inj (found.symm.trans selected)
          rw [same,liveDNA?,ammonia_resource_actual before.packet.source]
          rfl
      _ = (LiveStock cursor).filterMap liveDNA? := by
        have original := congrArg (List.filterMap liveDNA?) (List.zipIdx_map_fst 0 (LiveStock cursor))
        simpa only [List.filterMap_map,Function.comp_def] using original
  rw [List.filterMap_filterMap,List.filterMap_filterMap]
  change current.remaining.filterMap liveDNA? = (LiveStock cursor).filterMap liveDNA?
  exact erased

variable {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  {returned : NativePrepareNext paid continuation} {germ : NativeOriginGerm returned.occurrence}

/-- This decoder reads the actual variable native stock; the original cursor is
used only after the two consumed source slots have been proved DNA-invisible. -/
def native_resources (live : NativeSourceCurrent returned germ) : CPS1ResourceExecution.Stock :=
  (live.stock.filterMap (NativeAdoptionProbe.Species.live? returned germ)).filterMap liveResource?

def native_dna (live : NativeSourceCurrent returned germ) := readDNA (native_resources live)
def native_coding (live : NativeSourceCurrent returned germ) := readCoding (native_resources live)
def native_peptide (live : NativeSourceCurrent returned germ) : Option CPS1ResourceExecution.Peptide :=
  readPeptide (native_resources live)
def native_plan (live : NativeSourceCurrent returned germ) := readPlan (native_resources live)

def native_damage (live : NativeSourceCurrent returned germ) : CPS1BiologicalUpdate.ProteinDamageRead :=
  match native_peptide live with
  | none => .absentGenome
  | some peptide =>
    if peptide.2.length + 1 <
        SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.referenceProtein.length then
      .prematureStop (peptide.2.length + 1)
        SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.referenceProtein.length
    else .fullLength

theorem native_resources_remaining (live : NativeSourceCurrent returned germ) :
    native_resources live = current.remaining.filterMap liveResource? := by
  unfold native_resources
  rw [source_remaining live]

theorem native_resources_source (live : NativeSourceCurrent returned germ) :
    native_resources live = (unspentLive before.packet.source current.chainSlot).filterMap liveResource? := by
  rw [native_resources_remaining,current.remainingActual]

theorem native_dna_source (live : NativeSourceCurrent returned germ) :
    native_dna live = readDNA (liveResources cursor.native.current) := by
  unfold native_dna
  rw [native_resources_remaining]
  change ((current.remaining.filterMap liveResource?).filterMap dnaWord?).head? =
    (((LiveStock cursor).filterMap liveResource?).filterMap dnaWord?).head?
  exact congrArg List.head? (remaining_dna_words current)

theorem native_coding_source (live : NativeSourceCurrent returned germ) :
    native_coding live = readCoding (liveResources cursor.native.current) := by
  unfold native_coding readCoding
  rw [← native_dna_source live]
  rfl

theorem native_peptide_source (live : NativeSourceCurrent returned germ) :
    native_peptide live = CPS1BiologicalUpdate.actualGenePeptide cursor.native.current := by
  unfold native_peptide CPS1BiologicalUpdate.actualGenePeptide readPeptide
  rw [← native_coding_source live]
  rfl

theorem native_plan_source (live : NativeSourceCurrent returned germ) :
    native_plan live = readPlan (liveResources cursor.native.current) := by
  unfold native_plan readPlan
  rw [show readPeptide (liveResources cursor.native.current) = native_peptide live from (native_peptide_source live).symm]
  rfl

theorem native_damage_source (live : NativeSourceCurrent returned germ) :
    native_damage live = CPS1BiologicalUpdate.readProteinDamage cursor.native.current := by
  unfold native_damage CPS1BiologicalUpdate.readProteinDamage
  rw [native_peptide_source live]
  rfl

theorem native_resources_advance (live : NativeSourceCurrent returned germ) :
    native_resources (advanceSource live) = native_resources live :=
  (native_resources_remaining (advanceSource live)).trans (native_resources_remaining live).symm

theorem native_dna_advance (live : NativeSourceCurrent returned germ) :
    native_dna (advanceSource live) = native_dna live := congrArg readDNA (native_resources_advance live)

theorem native_coding_advance (live : NativeSourceCurrent returned germ) :
    native_coding (advanceSource live) = native_coding live := congrArg readCoding (native_resources_advance live)

theorem native_peptide_advance (live : NativeSourceCurrent returned germ) :
    native_peptide (advanceSource live) = native_peptide live := congrArg readPeptide (native_resources_advance live)

theorem native_plan_advance (live : NativeSourceCurrent returned germ) :
    native_plan (advanceSource live) = native_plan live := congrArg readPlan (native_resources_advance live)

theorem native_damage_advance (live : NativeSourceCurrent returned germ) :
    native_damage (advanceSource live) = native_damage live := by
  unfold native_damage
  rw [native_peptide_advance live]

end
end CPS1MaterialIncidence.NativeBodyGenomeProbe
