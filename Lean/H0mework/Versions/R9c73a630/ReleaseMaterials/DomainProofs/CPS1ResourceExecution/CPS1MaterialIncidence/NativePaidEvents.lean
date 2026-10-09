import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePaidSource

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

abbrev NativeEvent (source : Common before step raw) (current : NativeCurrent source) :=
  CPS1AddressedChemicalReaction.Event (NativeSpecies source current) NativeReaction

def eventIndex (_source : Common before step raw) : Nat :=
  cursor.native.current.ingress.atomic.source.nextEvent

def firstEvent {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeEvent source current :=
  ⟨eventIndex source,.phosphorylateBicarbonate,inputStock parent,
    [rawMaterial parent (firstFuel parent),rawMaterial parent (bicarbonateFuel parent)],
    [liveMaterial parent (ammoniaSlot source),rawMaterial parent (secondFuel parent)] ++ remainingParents parent⟩

def firstADP {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeMaterial source current :=
  .product (eventIndex source) 0 .phosphorylateBicarbonate (.molecule .adp) (firstEvent parent).consumed

def carboxyphosphate {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeMaterial source current :=
  .product (eventIndex source) 1 .phosphorylateBicarbonate (.molecule .carboxyphosphate) (firstEvent parent).consumed

def secondEvent {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeEvent source current :=
  ⟨eventIndex source+1,.formCarbamate,(firstEvent parent).after (products parent),
    [liveMaterial parent (ammoniaSlot source),carboxyphosphate parent],
    [firstADP parent,rawMaterial parent (secondFuel parent)] ++ remainingParents parent⟩

def carbamate {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeMaterial source current :=
  .product (eventIndex source+1) 0 .formCarbamate (.molecule .carbamate) (secondEvent parent).consumed

def phosphate {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeMaterial source current :=
  .product (eventIndex source+1) 1 .formCarbamate (.molecule .phosphate) (secondEvent parent).consumed

def proton {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeMaterial source current :=
  .product (eventIndex source+1) 2 .formCarbamate (.molecule .proton) (secondEvent parent).consumed

def thirdEvent {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeEvent source current :=
  ⟨eventIndex source+2,.phosphorylateCarbamate,(secondEvent parent).after (products parent),
    [rawMaterial parent (secondFuel parent),carbamate parent],
    [phosphate parent,proton parent,firstADP parent] ++ remainingParents parent⟩

def secondADP {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeMaterial source current :=
  .product (eventIndex source+2) 0 .phosphorylateCarbamate (.molecule .adp) (thirdEvent parent).consumed

def carbamoylPhosphate {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeMaterial source current :=
  .product (eventIndex source+2) 1 .phosphorylateCarbamate (.molecule .carbamoylPhosphate) (thirdEvent parent).consumed

theorem first_actual {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    CPS1AddressedChemicalReaction.fire? (reactants parent) (eventIndex source) .phosphorylateBicarbonate
      (inputStock parent) = .ok (firstEvent parent) := by
  simp [CPS1AddressedChemicalReaction.fire?,CPS1AddressedChemicalReaction.reserve_cons,
    CPS1AddressedChemicalReaction.reserve_nil,CPS1AddressedChemicalReaction.take_cons,
    CPS1AddressedChemicalReaction.Material.species,reactants,inputStock,chosenParents,rawMaterial,liveMaterial,firstEvent]

theorem first_after {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (firstEvent parent).after (products parent) =
      [firstADP parent,carboxyphosphate parent,liveMaterial parent (ammoniaSlot source),rawMaterial parent (secondFuel parent)] ++
        remainingParents parent := rfl

theorem second_actual {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    CPS1AddressedChemicalReaction.fire? (reactants parent) (eventIndex source+1) .formCarbamate
      ((firstEvent parent).after (products parent)) = .ok (secondEvent parent) := by
  rw [first_after]
  simp [CPS1AddressedChemicalReaction.fire?,CPS1AddressedChemicalReaction.reserve_cons,
    CPS1AddressedChemicalReaction.reserve_nil,CPS1AddressedChemicalReaction.take_cons,
    CPS1AddressedChemicalReaction.Material.species,reactants,firstADP,carboxyphosphate,
    rawMaterial,liveMaterial,secondEvent,first_after]

theorem second_after {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (secondEvent parent).after (products parent) =
      [carbamate parent,phosphate parent,proton parent,firstADP parent,rawMaterial parent (secondFuel parent)] ++
        remainingParents parent := rfl

theorem third_actual {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    CPS1AddressedChemicalReaction.fire? (reactants parent) (eventIndex source+2) .phosphorylateCarbamate
      ((secondEvent parent).after (products parent)) = .ok (thirdEvent parent) := by
  rw [second_after]
  simp [CPS1AddressedChemicalReaction.fire?,CPS1AddressedChemicalReaction.reserve_cons,
    CPS1AddressedChemicalReaction.reserve_nil,CPS1AddressedChemicalReaction.take_cons,
    CPS1AddressedChemicalReaction.Material.species,reactants,carbamate,phosphate,proton,firstADP,
    rawMaterial,thirdEvent,second_after]

theorem third_after {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (thirdEvent parent).after (products parent) =
      [secondADP parent,carbamoylPhosphate parent,phosphate parent,proton parent,firstADP parent] ++ remainingParents parent := by
  simp only [CPS1AddressedChemicalReaction.Event.after,CPS1AddressedChemicalReaction.Event.created,
    thirdEvent,last_products_generated,CPS1AddressedChemicalReaction.generatedProducts,
    List.zipIdx_cons,List.zipIdx_nil,List.map_cons,List.map_nil]
  rfl

theorem cp_created {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    carbamoylPhosphate parent ∈ (thirdEvent parent).created (products parent) := by
  simp only [CPS1AddressedChemicalReaction.Event.created,thirdEvent,last_products_generated,
    CPS1AddressedChemicalReaction.generatedProducts,List.zipIdx_cons,List.zipIdx_nil,List.map_cons,List.map_nil]
  exact List.mem_cons_of_mem _ (List.mem_cons_self)

theorem all_paid {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :
    (firstEvent parent).Valid (reactants parent) (products parent) ∧
    (secondEvent parent).Valid (reactants parent) (products parent) ∧
    (thirdEvent parent).Valid (reactants parent) (products parent) :=
  ⟨(CPS1AddressedChemicalReaction.fire_paid (reactants parent) (products parent) _ _ _ _ (first_actual parent)).2.2.2,
    (CPS1AddressedChemicalReaction.fire_paid (reactants parent) (products parent) _ _ _ _ (second_actual parent)).2.2.2,
    (CPS1AddressedChemicalReaction.fire_paid (reactants parent) (products parent) _ _ _ _ (third_actual parent)).2.2.2⟩

def paidExecution {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) :=
  CPS1AddressedChemicalReaction.run (reactants parent) (products parent) (eventIndex source)
    [.phosphorylateBicarbonate,.formCarbamate,.phosphorylateCarbamate] (inputStock parent)

theorem paid_execution_exact {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : paidExecution parent =
    ⟨[firstEvent parent,secondEvent parent,thirdEvent parent],[],
      (thirdEvent parent).after (products parent),none,eventIndex source+3⟩ := by
  simp only [paidExecution,CPS1AddressedChemicalReaction.run_cons,first_actual,second_actual,third_actual,
    CPS1AddressedChemicalReaction.run_nil]

theorem cp_in_actual_stock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : carbamoylPhosphate parent ∈ (paidExecution parent).stock := by
  rw [paid_execution_exact]
  exact List.mem_append_left _ (cp_created parent)

end
end CPS1MaterialIncidence.NativePaidEvent
