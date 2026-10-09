import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePaidEvents
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.StalledPhysical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativePaidEvent
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativeCarbamoyl

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

def liftLocalSpecies (species : CPS1LocalChemicalExecution.Species frame) : CPS1Deformation.Species frame :=
  .retained (.retained (.retained (.retained (.retained (.retained (.retained (.retained species)))))))

def liveSpecies : CPS1ReactiveField.LiveMaterial frame → CPS1Deformation.Species frame
  | .old species => species
  | .reactive material => liftLocalSpecies material.species

theorem live_local_species (material : CPS1ReactiveField.LiveMaterial frame)
    (species : CPS1LocalChemicalExecution.Species frame)
    (actual : CPS1BiologicalUpdate.liveLocal? material = some species) : liveSpecies material = liftLocalSpecies species := by
  cases material with
  | reactive material =>
    cases material <;> simp_all [CPS1BiologicalUpdate.liveLocal?,liveSpecies,
      CPS1AddressedChemicalReaction.Material.species]
  | old old =>
    unfold CPS1BiologicalUpdate.liveLocal? at actual
    split at actual <;> simp_all [liveSpecies,liftLocalSpecies]

def fuelSpecies (entry : FuelKind × Nat) : CPS1Deformation.Species frame :=
  liftLocalSpecies (CPS1LocalChemicalExecution.molecule frame (localSpecies entry.1))

def readSpecies {source : Common before step raw} {current : NativeCurrent source} :
    NativeSpecies source current → CPS1Deformation.Species frame
  | .live slot => liveSpecies ((LiveStock cursor).get slot)
  | .fuel entry => fuelSpecies entry.1
  | .active state => .deformed state.1
  | .molecule kind => liftLocalSpecies (CPS1LocalChemicalExecution.molecule frame kind)

-- The reaction index remains native: ElectronicSource has no generic retained chemical reaction.
abbrev ReadMaterial (frame : CPS1Recycling.Frame) :=
  CPS1AddressedChemicalReaction.Material (CPS1Deformation.Species frame) NativeReaction
abbrev ReadEvent (frame : CPS1Recycling.Frame) :=
  CPS1AddressedChemicalReaction.Event (CPS1Deformation.Species frame) NativeReaction

def readMaterial {source : Common before step raw} {current : NativeCurrent source} :
    NativeMaterial source current → ReadMaterial frame
  | .inherited species => .inherited (readSpecies species)
  | .raw batch ordinal species => .raw batch ordinal (readSpecies species)
  | .product event ordinal reaction species parents =>
    .product event ordinal reaction (readSpecies species) (parents.map readMaterial)

theorem read_material_species {source : Common before step raw} {current : NativeCurrent source}
    (material : NativeMaterial source current) : (readMaterial material).species = readSpecies material.species := by
  cases material <;> simp only [readMaterial,CPS1AddressedChemicalReaction.Material.species]

theorem forget_read {source : Common before step raw} {current : NativeCurrent source}
    (stock : List (NativeMaterial source current)) :
    CPS1AddressedChemicalReaction.forget (stock.map readMaterial) =
      stock.map (fun material => readSpecies material.species) := by
  simp only [CPS1AddressedChemicalReaction.forget,List.map_map,Function.comp_def,read_material_species]

theorem read_ammonia {source : Common before step raw} {current : NativeCurrent source} :
    readSpecies (source := source) (current := current) (.live (ammoniaSlot source)) =
      liftLocalSpecies (CPS1LocalChemicalExecution.molecule frame .ammonia) :=
  live_local_species _ _ before.packet.source.ammonia.species

def readReactants {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (reaction : NativeReaction) : CPS1Deformation.Stock frame :=
  (reactants parent reaction).map readSpecies

def readProducts {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (reaction : NativeReaction) : CPS1Deformation.Stock frame :=
  (products parent reaction).map readSpecies

def chemicalStep : NativeReaction → CPS1LocalChemicalExecution.Chemistry.Step
  | .phosphorylateBicarbonate => .phosphorylateBicarbonate
  | .formCarbamate => .formCarbamate
  | .phosphorylateCarbamate => .phosphorylateCarbamate

theorem read_reactants_local {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (reaction : NativeReaction) : readReactants parent reaction =
    (CPS1LocalChemicalExecution.Reaction.reactants frame (.chemical (chemicalStep reaction))).map liftLocalSpecies := by
  cases reaction with
  | phosphorylateBicarbonate => rfl
  | formCarbamate =>
    change [readSpecies (.live (ammoniaSlot source)),liftLocalSpecies (CPS1LocalChemicalExecution.molecule frame .carboxyphosphate)] = _
    rw [read_ammonia]
    rfl
  | phosphorylateCarbamate => rfl

theorem read_products_local {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (reaction : NativeReaction) : readProducts parent reaction =
    (CPS1LocalChemicalExecution.Reaction.products frame (.chemical (chemicalStep reaction))).map liftLocalSpecies := by
  cases reaction with
  | phosphorylateBicarbonate => rfl
  | formCarbamate => rfl
  | phosphorylateCarbamate => rw [readProducts,last_products_generated]; rfl

def readEvent {source : Common before step raw} {current : NativeCurrent source}
    (event : NativeEvent source current) : ReadEvent frame :=
  ⟨event.index,event.reaction,event.before.map readMaterial,event.consumed.map readMaterial,event.remainder.map readMaterial⟩

theorem read_created {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (event : NativeEvent source current) :
    (event.created (products parent)).map readMaterial = (readEvent event).created (readProducts parent) := by
  simp only [CPS1AddressedChemicalReaction.Event.created,CPS1AddressedChemicalReaction.generatedProducts,
    readEvent,readProducts,List.zipIdx_map,List.map_map,Function.comp_def,readMaterial,Prod.map,id_eq]

theorem read_after {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (event : NativeEvent source current) :
    (event.after (products parent)).map readMaterial = (readEvent event).after (readProducts parent) := by
  simp only [CPS1AddressedChemicalReaction.Event.after,List.map_append,read_created,readEvent]

theorem first_read_actual {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    CPS1AddressedChemicalReaction.fire? (readReactants parent) (eventIndex source) .phosphorylateBicarbonate
      ((inputStock parent).map readMaterial) = .ok (readEvent (firstEvent parent)) := by
  simp [CPS1AddressedChemicalReaction.fire?,CPS1AddressedChemicalReaction.reserve_cons,
    CPS1AddressedChemicalReaction.reserve_nil,CPS1AddressedChemicalReaction.take_cons,
    CPS1AddressedChemicalReaction.Material.species,readReactants,reactants,inputStock,chosenParents,
    readEvent,firstEvent,rawMaterial,liveMaterial,readMaterial,readSpecies,fuelSpecies,
    firstFuel,bicarbonateFuel,localSpecies,liftLocalSpecies]

theorem second_read_actual {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    CPS1AddressedChemicalReaction.fire? (readReactants parent) (eventIndex source+1) .formCarbamate
      ((readEvent (firstEvent parent)).after (readProducts parent)) = .ok (readEvent (secondEvent parent)) := by
  rw [← read_after,first_after]
  have ammonia := read_ammonia (source := source) (current := current)
  change liveSpecies ((LiveStock cursor).get (ammoniaSlot source)) = _ at ammonia
  simp only [List.get_eq_getElem] at ammonia
  simp [CPS1AddressedChemicalReaction.fire?,CPS1AddressedChemicalReaction.reserve_cons,
    CPS1AddressedChemicalReaction.reserve_nil,CPS1AddressedChemicalReaction.take_cons,
    CPS1AddressedChemicalReaction.Material.species,readReactants,reactants,
    readEvent,secondEvent,first_after,firstADP,carboxyphosphate,rawMaterial,liveMaterial,
    readMaterial,ammonia,readSpecies,liftLocalSpecies,CPS1LocalChemicalExecution.molecule,CPS1StockRecursion.Dictionary.old]

theorem third_read_actual {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    CPS1AddressedChemicalReaction.fire? (readReactants parent) (eventIndex source+2) .phosphorylateCarbamate
      ((readEvent (secondEvent parent)).after (readProducts parent)) = .ok (readEvent (thirdEvent parent)) := by
  rw [← read_after,second_after]
  simp [CPS1AddressedChemicalReaction.fire?,CPS1AddressedChemicalReaction.reserve_cons,
    CPS1AddressedChemicalReaction.reserve_nil,CPS1AddressedChemicalReaction.take_cons,
    CPS1AddressedChemicalReaction.Material.species,readReactants,reactants,
    readEvent,thirdEvent,second_after,carbamate,phosphate,proton,firstADP,rawMaterial,
    readMaterial,readSpecies,fuelSpecies,secondFuel,localSpecies,liftLocalSpecies,CPS1LocalChemicalExecution.molecule,CPS1StockRecursion.Dictionary.old]

theorem read_all_paid {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (readEvent (firstEvent parent)).Valid (readReactants parent) (readProducts parent) ∧
    (readEvent (secondEvent parent)).Valid (readReactants parent) (readProducts parent) ∧
    (readEvent (thirdEvent parent)).Valid (readReactants parent) (readProducts parent) :=
  ⟨(CPS1AddressedChemicalReaction.fire_paid _ _ _ _ _ _ (first_read_actual parent)).2.2.2,
    (CPS1AddressedChemicalReaction.fire_paid _ _ _ _ _ _ (second_read_actual parent)).2.2.2,
    (CPS1AddressedChemicalReaction.fire_paid _ _ _ _ _ _ (third_read_actual parent)).2.2.2⟩

def readExecution {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :=
  CPS1AddressedChemicalReaction.run (readReactants parent) (readProducts parent) (eventIndex source)
    [.phosphorylateBicarbonate,.formCarbamate,.phosphorylateCarbamate] ((inputStock parent).map readMaterial)

theorem read_execution_exact {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : readExecution parent =
    ⟨[readEvent (firstEvent parent),readEvent (secondEvent parent),readEvent (thirdEvent parent)],[],
      (readEvent (thirdEvent parent)).after (readProducts parent),none,eventIndex source+3⟩ := by
  simp only [readExecution,CPS1AddressedChemicalReaction.run_cons,first_read_actual,second_read_actual,third_read_actual,
    CPS1AddressedChemicalReaction.run_nil]

theorem read_execution_stock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : (readExecution parent).stock = (paidExecution parent).stock.map readMaterial := by
  rw [read_execution_exact,paid_execution_exact]
  exact (read_after parent (thirdEvent parent)).symm

def paidStock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : CPS1Deformation.Stock frame :=
  CPS1AddressedChemicalReaction.forget (readExecution parent).stock

theorem cp_created_read {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    readMaterial (carbamoylPhosphate parent) ∈ (readEvent (thirdEvent parent)).created (readProducts parent) := by
  rw [← read_created]
  exact List.mem_map_of_mem (cp_created parent)

theorem cp_in_paid_stock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : deformedCP frame ∈ paidStock parent := by
  have mapped : readMaterial (carbamoylPhosphate parent) ∈ (readExecution parent).stock := by
    rw [read_execution_stock]
    exact List.mem_map_of_mem (cp_in_actual_stock parent)
  have identity : (readMaterial (carbamoylPhosphate parent)).species = deformedCP frame := by
    rw [read_material_species]
    rfl
  rw [← identity]
  exact List.mem_map_of_mem (f := CPS1AddressedChemicalReaction.Material.species) mapped

def sourceStock (source : Common before step raw) (current : NativeCurrent source) : CPS1Deformation.Stock frame :=
  (oldCurrent source).stock ++
    cursor.native.current.ingress.atomic.source.stock.map (fun material => liftLocalSpecies material.species) ++
    current.materializedRaw.map fuelSpecies

theorem live_indices_exact (stock : List (CPS1ReactiveField.LiveMaterial frame)) :
    (List.finRange stock.length).map stock.get = stock := by
  rw [← List.ofFn_eq_map,List.ofFn_get]

theorem parent_stock_source {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (CPS1AddressedChemicalReaction.forget ((parentStock parent).map readMaterial)).Perm (sourceStock source current) := by
  rw [forget_read]
  simp only [parentStock,List.map_append,List.map_map,Function.comp_def,liveMaterial,rawMaterial,
    CPS1AddressedChemicalReaction.Material.species,readSpecies]
  have live : (List.finRange (LiveStock cursor).length).map (fun slot => liveSpecies ((LiveStock cursor).get slot)) =
      (LiveStock cursor).map liveSpecies := by
    change (List.finRange (LiveStock cursor).length).map (liveSpecies ∘ (LiveStock cursor).get) = _
    rw [← List.map_map,live_indices_exact]
  rw [live]
  simp only [LiveStock,CPS1ReactiveField.liveStock,List.map_append,List.map_map,Function.comp_def,liveSpecies,
    List.attach_map_val]
  unfold activeMaterials
  split
  · simp only [List.map_nil,List.nil_append,CPS1ReactiveField.oldResidual,oldCurrent,sourceStock]
    rename_i selected
    rw [selected]
    simpa only [List.map_id_fun',id_eq,sourceStock,oldCurrent] using (List.Perm.refl (sourceStock source current))
  · rename_i state selected
    simp only [List.map_cons,List.map_nil,CPS1AddressedChemicalReaction.Material.species,
      CPS1ReactiveField.oldResidual,oldCurrent,sourceStock,selected]
    simpa only [List.map_id_fun',id_eq,CPS1AddressedChemicalReaction.Material.species,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using
      ((List.perm_cons_erase (CPS1ReactiveField.held_deformed_member _ _ selected)).symm.append_right
        (cursor.native.current.ingress.atomic.source.stock.map (fun material => liftLocalSpecies material.species))).append_right
          (current.materializedRaw.map fuelSpecies)

theorem input_stock_source {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (CPS1AddressedChemicalReaction.forget ((inputStock parent).map readMaterial)).Perm (sourceStock source current) := by
  have whole := ((input_is_whole_parent_stock parent).map readMaterial).map CPS1AddressedChemicalReaction.Material.species
  exact whole.symm.trans (parent_stock_source parent)

-- Native replacement consumes the chain/NH3 slots exactly once. This restriction never reconstitutes a physical token.
def untouchedSlots {source : Common before step raw} (current : NativeCurrent source) : List (Fin (LiveStock cursor).length) :=
  ((List.finRange (LiveStock cursor).length).erase current.chainSlot).erase (ammoniaSlot source)

theorem indexed_live_exact (stock : List (CPS1ReactiveField.LiveMaterial frame)) :
    (List.finRange stock.length).map (fun slot => (stock.get slot,slot.val)) = stock.zipIdx := by
  apply List.ext_getElem
  · simp
  · intro i first second
    simp

theorem filter_map_guard {α β : Type} (entries : List α) (predicate : α → Prop)
    [DecidablePred predicate] (read : α → β) :
    (entries.filter (fun entry => decide (predicate entry))).map read =
      entries.filterMap (fun entry => if predicate entry then some (read entry) else none) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => by_cases selected : predicate entry <;> simp [selected,ih]

theorem untouched_slots_actual {source : Common before step raw} (current : NativeCurrent source) :
    (untouchedSlots current).map (LiveStock cursor).get = current.remaining := by
  rw [current.remainingActual]
  unfold untouchedSlots unspentLive
  rw [List.Nodup.erase_eq_filter (List.nodup_finRange _) current.chainSlot,
    List.Nodup.erase_eq_filter ((List.nodup_finRange _).filter _) (ammoniaSlot source),List.filter_filter]
  rw [← indexed_live_exact,List.filterMap_map]
  simp only [Function.comp_def]
  have predicate : (fun slot : Fin (LiveStock cursor).length => slot != ammoniaSlot source && slot != current.chainSlot) =
      (fun slot => decide (slot.val ≠ current.chainSlot.val ∧ slot.val ≠ before.packet.source.ammonia.slot.val)) := by
    funext slot
    apply Bool.eq_iff_iff.mpr
    simp [ammoniaSlot,Fin.ext_iff,and_comm]
  rw [predicate,filter_map_guard]
  apply List.filterMap_congr
  intro slot _
  by_cases consumed : slot.val = current.chainSlot.val ∨ slot.val = before.packet.source.ammonia.slot.val
  · have denied : ¬ (slot.val ≠ current.chainSlot.val ∧ slot.val ≠ before.packet.source.ammonia.slot.val) := by tauto
    simp only [if_pos consumed,if_neg denied]
  · simp only [if_neg consumed,if_pos (not_or.mp consumed)]

theorem native_live_partition {source : Common before step raw} (current : NativeCurrent source) :
    (LiveStock cursor).Perm
      ([(LiveStock cursor).get current.chainSlot,(LiveStock cursor).get (ammoniaSlot source)] ++ current.remaining) := by
  have chosen : ([current.chainSlot,ammoniaSlot source] : List (Fin (LiveStock cursor).length)).Nodup := by
    simp [ammoniaSlot,current.parentsDistinct]
  have held : ∀ slot ∈ ([current.chainSlot,ammoniaSlot source] : List (Fin (LiveStock cursor).length)),
      slot ∈ List.finRange (LiveStock cursor).length := by simp
  have selected := (select_parents_perm _ _ chosen held).map (LiveStock cursor).get
  simpa only [live_indices_exact,List.map_append,List.map_cons,List.map_nil,eraseParents,
    ← untouched_slots_actual current,untouchedSlots] using selected


theorem native_paid_whole {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (parentStock parent ++ (paidExecution parent).fired.flatMap (CPS1AddressedChemicalReaction.Event.created (products parent))).Perm
      ((paidExecution parent).stock ++ (paidExecution parent).fired.flatMap CPS1AddressedChemicalReaction.Event.consumed) := by
  have history := CPS1AddressedChemicalReaction.run_path (reactants parent) (products parent) (eventIndex source)
    [.phosphorylateBicarbonate,.formCarbamate,.phosphorylateCarbamate] (inputStock parent)
  exact ((input_is_whole_parent_stock parent).append_right _).trans
    (CPS1AddressedChemicalReaction.path_whole _ _ _ _ _ _ history)

def liveSlot? {source : Common before step raw} {current : NativeCurrent source} :
    NativeMaterial source current → Option (Fin (LiveStock cursor).length)
  | .inherited (.live slot) => some slot
  | _ => none

theorem live_parent_slots {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : (parentStock parent).filterMap liveSlot? = List.finRange (LiveStock cursor).length := by
  simp only [parentStock,List.filterMap_append,List.filterMap_map,Function.comp_def,liveMaterial,rawMaterial,liveSlot?,
    List.filterMap_some]
  have rawEmpty : List.filterMap (fun (_ : FuelAt current) => (none : Option (Fin (LiveStock cursor).length)))
      current.materializedRaw.attach = [] := by simp only [List.filterMap_eq_nil_iff,implies_true]
  rw [rawEmpty,List.append_nil]
  unfold activeMaterials
  split <;> simp only [List.filterMap_nil,List.filterMap_cons,liveSlot?,List.nil_append]

theorem live_created_empty {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (event : NativeEvent source current) :
    (event.created (products parent)).filterMap liveSlot? = [] := by
  simp only [CPS1AddressedChemicalReaction.Event.created,CPS1AddressedChemicalReaction.generatedProducts,
    List.filterMap_map,Function.comp_def,liveSlot?,List.filterMap_eq_nil_iff,implies_true]

theorem paid_live_slots {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    ((paidExecution parent).stock.filterMap liveSlot?).Perm (current.chainSlot :: untouchedSlots current) := by
  classical
  have whole := (native_paid_whole parent).filterMap liveSlot?
  have noCreated : ((paidExecution parent).fired.flatMap (CPS1AddressedChemicalReaction.Event.created (products parent))).filterMap liveSlot? = [] := by
    simp only [List.filterMap_flatMap,live_created_empty,List.flatMap_eq_nil_iff,implies_true]
  have consumed : ((paidExecution parent).fired.flatMap CPS1AddressedChemicalReaction.Event.consumed).filterMap liveSlot? = [ammoniaSlot source] := by
    rw [paid_execution_exact]
    simp only [List.flatMap_cons,List.flatMap_nil,firstEvent,secondEvent,thirdEvent,List.filterMap_append,
      List.filterMap_cons,List.filterMap_nil,rawMaterial,liveMaterial,carboxyphosphate,carbamate,liveSlot?,List.nil_append,List.append_nil]
  simp only [List.filterMap_append,live_parent_slots,noCreated,consumed,List.append_nil] at whole
  have initial := List.perm_cons_erase (List.mem_finRange (ammoniaSlot source))
  have cancelled : ((paidExecution parent).stock.filterMap liveSlot?).Perm
      ((List.finRange (LiveStock cursor).length).erase (ammoniaSlot source)) :=
    (List.perm_append_left_iff [ammoniaSlot source]).mp
      (List.perm_append_comm.trans (whole.symm.trans initial))
  have chain : current.chainSlot ∈ (List.finRange (LiveStock cursor).length).erase (ammoniaSlot source) :=
    (List.mem_erase_of_ne current.parentsDistinct).mpr (List.mem_finRange _)
  have selected := List.perm_cons_erase chain
  have ordered : (((List.finRange (LiveStock cursor).length).erase (ammoniaSlot source)).erase current.chainSlot) = untouchedSlots current := by
    exact List.erase_comm (ammoniaSlot source) current.chainSlot
  exact cancelled.trans (ordered ▸ selected)

theorem actual_remaining_after {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (((paidExecution parent).stock.filterMap liveSlot?).map (LiveStock cursor).get).Perm
      ((LiveStock cursor).get current.chainSlot :: current.remaining) := by
  simpa only [List.map_cons,untouched_slots_actual] using (paid_live_slots parent).map (LiveStock cursor).get

theorem native_inventory_commutes {source : Common before step raw} (current : NativeCurrent source) :
    inventory current = StockItem.evolved current ::
      ((untouchedSlots current).map (LiveStock cursor).get).map (StockItem.remaining (source := source)) := by
  rw [untouched_slots_actual]
  rfl

def causalLeaves {source : Common before step raw} {current : NativeCurrent source} :
    NativeMaterial source current → List (NativeMaterial source current)
  | .product _ _ _ _ parents => parents.flatMap causalLeaves
  | material => [material]

theorem cp_causal_parents {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : causalLeaves (carbamoylPhosphate parent) =
      [rawMaterial parent (secondFuel parent),liveMaterial parent (ammoniaSlot source),
        rawMaterial parent (firstFuel parent),rawMaterial parent (bicarbonateFuel parent)] := by
  simp only [carbamoylPhosphate,thirdEvent,carbamate,secondEvent,carboxyphosphate,firstEvent,
    causalLeaves,List.flatMap_cons,List.flatMap_nil,rawMaterial,liveMaterial,
    List.singleton_append,List.append_nil]

def chainSpecies {source : Common before step raw} (current : NativeCurrent source) : CPS1Deformation.Species frame :=
  readSpecies (source := source) (current := current) (.live current.chainSlot)

theorem chain_in_remainder {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : liveMaterial parent current.chainSlot ∈ remainingParents parent := by
  classical
  have held : liveMaterial parent current.chainSlot ∈ parentStock parent :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
      ⟨current.chainSlot,List.mem_finRange _,rfl⟩))
  have first : liveMaterial parent current.chainSlot ≠ rawMaterial parent (firstFuel parent) := by
    simp only [liveMaterial,rawMaterial,ne_eq,reduceCtorEq,not_false_eq_true]
  have bct : liveMaterial parent current.chainSlot ≠ rawMaterial parent (bicarbonateFuel parent) := by
    simp only [liveMaterial,rawMaterial,ne_eq,reduceCtorEq,not_false_eq_true]
  have ammonia : liveMaterial parent current.chainSlot ≠ liveMaterial parent (ammoniaSlot source) := by
    intro same
    have slots := NativeSpecies.live.inj (CPS1AddressedChemicalReaction.Material.inherited.inj same)
    exact current.parentsDistinct slots
  have second : liveMaterial parent current.chainSlot ≠ rawMaterial parent (secondFuel parent) := by
    simp only [liveMaterial,rawMaterial,ne_eq,reduceCtorEq,not_false_eq_true]
  exact (List.mem_erase_of_ne second).mpr ((List.mem_erase_of_ne ammonia).mpr
    ((List.mem_erase_of_ne bct).mpr ((List.mem_erase_of_ne first).mpr held)))

theorem chain_in_paid_stock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : chainSpecies current ∈ paidStock parent := by
  have native : liveMaterial parent current.chainSlot ∈ (paidExecution parent).stock := by
    rw [paid_execution_exact,third_after]
    exact List.mem_append_right _ (chain_in_remainder parent)
  have mapped : readMaterial (liveMaterial parent current.chainSlot) ∈ (readExecution parent).stock := by
    rw [read_execution_stock]
    exact List.mem_map_of_mem native
  have identity : (readMaterial (liveMaterial parent current.chainSlot)).species = chainSpecies current := by
    rw [read_material_species]
    rfl
  rw [← identity]
  exact List.mem_map_of_mem (f := CPS1AddressedChemicalReaction.Material.species) mapped

theorem chain_ne_cp {source : Common before step raw} (current : NativeCurrent source) :
    chainSpecies current ≠ deformedCP frame := by
  intro same
  have owned := current.chainSlotActual
  cases actual : (LiveStock cursor).get current.chainSlot with
  | reactive material => simp only [actual,Classical.ownedLive?] at owned; cases owned
  | old species =>
    have identity : species = deformedCP frame := by
      simpa only [chainSpecies,readSpecies,actual,liveSpecies] using same
    rw [actual,Classical.ownedLive?,identity] at owned
    cases owned

-- Moving the selected source restriction to the head changes no material occurrence.
def canonicalStock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : CPS1Deformation.Stock frame :=
  chainSpecies current :: (paidStock parent).erase (chainSpecies current)

theorem canonical_paid_stock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : (paidStock parent).Perm (canonicalStock parent) :=
  List.perm_cons_erase (chain_in_paid_stock parent)

theorem cp_in_canonical_stock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : deformedCP frame ∈ canonicalStock parent :=
  (canonical_paid_stock parent).mem_iff.mp (cp_in_paid_stock parent)

def paidCursor {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : CPS1Deformation.Source.Cursor frame :=
  {oldCurrent source with stock := canonicalStock parent}

def pendingExecution {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : CPS1Deformation.Execution frame :=
  CPS1Deformation.execute frame
    (CPS1Deformation.Source.program frame (CPS1Deformation.Source.heldCarrier frame (canonicalStock parent))
      (oldCurrent source).pending) (canonicalStock parent)

def nextCursor {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : CPS1Deformation.Source.Cursor frame :=
  CPS1Deformation.Source.advance frame (paidCursor parent) [] []

theorem paid_cursor_source {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (paidCursor parent).pending = (oldCurrent source).pending ∧
    (paidCursor parent).stages = (oldCurrent source).stages ∧
    (paidCursor parent).cut = (oldCurrent source).cut ∧ deformedCP frame ∈ (paidCursor parent).stock :=
  ⟨rfl,rfl,rfl,cp_in_canonical_stock parent⟩

theorem next_cursor_exact {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : nextCursor parent =
    ⟨(pendingExecution parent).stock,(oldCurrent source).pending.drop (pendingExecution parent).fired.length,
      (oldCurrent source).stages ++ [pendingExecution parent],(pendingExecution parent).missing⟩ := by
  simp only [nextCursor,CPS1Deformation.Source.advance,paidCursor,List.map_nil,List.flatMap_nil,
    List.append_nil,List.nil_append,pendingExecution]

def wrappedJoint (joint : CPS1EnzymeBath.Joint.State frame) : CPS1Deformation.Species frame :=
  .retained (.retained (.retained (.retained (.retained (.joint joint)))))

def jointAttach (joint : CPS1EnzymeBath.Joint.State frame) : CPS1Deformation.Reaction frame :=
  .retained (.retained (.retained (.retained (.jointAttach joint .carbamoylPhosphate))))

def attachmentAfter {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (joint : CPS1EnzymeBath.Joint.State frame) : CPS1Deformation.Stock frame :=
  CPS1Deformation.Reaction.products frame (jointAttach joint) ++
    ((canonicalStock parent).erase (wrappedJoint joint)).erase (deformedCP frame)

theorem attachment_actual {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (joint : CPS1EnzymeBath.Joint.State frame)
    (selected : chainSpecies current = wrappedJoint joint) :
    CPS1ResourceExecution.Inventory.fire (CPS1Deformation.Reaction.reactants frame) (CPS1Deformation.Reaction.products frame)
      (jointAttach joint) (canonicalStock parent) = .ok (attachmentAfter parent joint) := by
  have required : CPS1Deformation.Reaction.reactants frame (jointAttach joint) =
      [wrappedJoint joint,deformedCP frame] := by
    simp only [jointAttach,wrappedJoint,CPS1Deformation.Reaction.reactants,CPS1MolecularFrame.Reaction.reactants,
      CPS1Following.Reaction.reactants,CPS1QuantumNuclear.Reaction.reactants,CPS1ElectronicSource.Reaction.reactants,
      List.map_cons,List.map_nil]
    rfl
  have chain : wrappedJoint joint ∈ canonicalStock parent := by
    rw [canonicalStock,selected]
    exact List.mem_cons_self
  have cp : deformedCP frame ∈ (canonicalStock parent).erase (wrappedJoint joint) :=
    (List.mem_erase_of_ne (by simpa only [← selected] using (chain_ne_cp current).symm)).mpr (cp_in_canonical_stock parent)
  simp only [CPS1ResourceExecution.Inventory.fire,required,CPS1ResourceExecution.Inventory.consume,
    if_pos chain,if_pos cp,attachmentAfter]

theorem pending_attachment_fired {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) (joint : CPS1EnzymeBath.Joint.State frame)
    (rest : List CPS1Deformation.Source.RawAction)
    (selected : chainSpecies current = wrappedJoint joint) (requested : (oldCurrent source).pending = deformedAttach :: rest) :
    ∃ later, (pendingExecution parent).fired = jointAttach joint :: later := by
  have held : CPS1Deformation.Source.heldCarrier frame (canonicalStock parent) =
      some (.molecular (.following (.reference (.joint joint)))) := by
    rw [canonicalStock,selected]
    rfl
  have program : CPS1Deformation.Source.program frame
      (CPS1Deformation.Source.heldCarrier frame (canonicalStock parent)) (oldCurrent source).pending =
      jointAttach joint :: CPS1Deformation.Source.program frame
        (some (.molecular (.following (.reference (.joint (CPS1EnzymeBath.Joint.attach frame joint .carbamoylPhosphate)))))) rest := by
    rw [requested,held]
    rfl
  rw [pendingExecution,program,CPS1Deformation.execute,CPS1ResourceExecution.Inventory.execute_cons,attachment_actual parent joint selected]
  exact ⟨_,rfl⟩

-- This disposition is the coarse pending consumer; the Native PostState below remains its separate physical source.
inductive PendingDisposition {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current)
  | cpConsumed (joint : CPS1EnzymeBath.Joint.State frame) (rest : List CPS1Deformation.Source.RawAction)
      (selected : chainSpecies current = wrappedJoint joint)
      (requested : (oldCurrent source).pending = deformedAttach :: rest)
      (actual : CPS1ResourceExecution.Inventory.fire (CPS1Deformation.Reaction.reactants frame)
        (CPS1Deformation.Reaction.products frame) (jointAttach joint) (canonicalStock parent) = .ok (attachmentAfter parent joint))
      (fired : ∃ later, (pendingExecution parent).fired = jointAttach joint :: later)
  | otherPending (actual : ¬ ∃ (joint : CPS1EnzymeBath.Joint.State frame) (rest : List CPS1Deformation.Source.RawAction),
      chainSpecies current = wrappedJoint joint ∧ (oldCurrent source).pending = deformedAttach :: rest)

theorem pending_disposition_nonempty {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : Nonempty (PendingDisposition parent) := by
  classical
  by_cases applicable : ∃ (joint : CPS1EnzymeBath.Joint.State frame) (rest : List CPS1Deformation.Source.RawAction),
      chainSpecies current = wrappedJoint joint ∧ (oldCurrent source).pending = deformedAttach :: rest
  · obtain ⟨joint,rest,selected,requested⟩ := applicable
    exact ⟨.cpConsumed joint rest selected requested (attachment_actual parent joint selected)
      (pending_attachment_fired parent joint rest selected requested)⟩
  · exact ⟨.otherPending applicable⟩

def returnedSource {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : CPS1Deformation.Source.Occurrence frame :=
  {cursor.native.current.old with current := nextCursor parent}

structure SourceGeneratedPaidReturn (source : Common before step raw) (current : NativeCurrent source) where
  parent : ParentSource source current
  paid : (readEvent (firstEvent parent)).Valid (readReactants parent) (readProducts parent) ∧
    (readEvent (secondEvent parent)).Valid (readReactants parent) (readProducts parent) ∧
    (readEvent (thirdEvent parent)).Valid (readReactants parent) (readProducts parent)
  sourcePartition : (CPS1AddressedChemicalReaction.forget ((inputStock parent).map readMaterial)).Perm (sourceStock source current)
  nativeRemaining : (untouchedSlots current).map (LiveStock cursor).get = current.remaining
  remainingAfter : (((paidExecution parent).stock.filterMap liveSlot?).map (LiveStock cursor).get).Perm
    ((LiveStock cursor).get current.chainSlot :: current.remaining)
  nativeWhole : (parentStock parent ++ (paidExecution parent).fired.flatMap (CPS1AddressedChemicalReaction.Event.created (products parent))).Perm
    ((paidExecution parent).stock ++ (paidExecution parent).fired.flatMap CPS1AddressedChemicalReaction.Event.consumed)
  canonical : (paidStock parent).Perm (canonicalStock parent)
  cpCreated : readMaterial (carbamoylPhosphate parent) ∈ (readEvent (thirdEvent parent)).created (readProducts parent)
  oldSource : (paidCursor parent).pending = (oldCurrent source).pending ∧
    (paidCursor parent).stages = (oldCurrent source).stages ∧ (paidCursor parent).cut = (oldCurrent source).cut ∧
    deformedCP frame ∈ (paidCursor parent).stock
  pending : PendingDisposition parent
  actualNext : nextCursor parent =
    ⟨(pendingExecution parent).stock,(oldCurrent source).pending.drop (pendingExecution parent).fired.length,
      (oldCurrent source).stages ++ [pendingExecution parent],(pendingExecution parent).missing⟩
  physical : NativeAmmoniaDynamics.PostState current
  physicalActual : physical = parent.products.dynamics.result.next
  physicalAccount : physical.energy + physical.reserve =
    (NativeAmmoniaDynamics.initialState parent.products.dynamics.origin).energy +
    (NativeAmmoniaDynamics.initialState parent.products.dynamics.origin).reserve

theorem source_generated_paid_return (source : Common before step raw) (current : NativeCurrent source) :
    Nonempty (SourceGeneratedPaidReturn source current) := by
  obtain ⟨parent⟩ := source_parent_nonempty source current
  obtain ⟨pending⟩ := pending_disposition_nonempty parent
  exact ⟨⟨parent,read_all_paid parent,input_stock_source parent,untouched_slots_actual current,actual_remaining_after parent,native_paid_whole parent,
    canonical_paid_stock parent,cp_created_read parent,paid_cursor_source parent,pending,next_cursor_exact parent,
    parent.products.dynamics.result.next,rfl,NativeAmmoniaDynamics.disposition_account parent.products.dynamics.result⟩⟩

end
end CPS1MaterialIncidence.NativePaidEvent
