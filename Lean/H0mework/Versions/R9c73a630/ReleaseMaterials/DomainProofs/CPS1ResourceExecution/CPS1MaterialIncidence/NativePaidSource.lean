import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualCarbamoylProducts
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedChemicalReaction.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Partner
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.ReadControls

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

abbrev ChemicalKind := CPS1LocalChemicalExecution.Chemistry.Molecule

structure ParentSource (source : Common before step raw) (current : NativeCurrent source) where
  products : SourceGeneratedCarbamoyl source current

theorem source_parent_nonempty (source : Common before step raw) (current : NativeCurrent source) :
    Nonempty (ParentSource source current) := by
  obtain ⟨products⟩ := source_generated_carbamoyl_products source current
  exact ⟨⟨products⟩⟩

abbrev FuelAt {source : Common before step raw} (current : NativeCurrent source) :=
  {entry : FuelKind × Nat // entry ∈ current.materializedRaw}

inductive NativeSpecies (source : Common before step raw) (current : NativeCurrent source)
  | live (slot : Fin (LiveStock cursor).length)
  | fuel (entry : FuelAt current)
  | active (state : {state : CPS1Deformation.Material frame //
      CPS1ReactiveField.heldDeformed cursor.native.current.old.current.stock = some state})
  | molecule (kind : ChemicalKind)

instance {source : Common before step raw} {current : NativeCurrent source} :
    DecidableEq (NativeSpecies source current) := Classical.decEq _

inductive NativeReaction | phosphorylateBicarbonate | formCarbamate | phosphorylateCarbamate
  deriving DecidableEq

abbrev NativeMaterial (source : Common before step raw) (current : NativeCurrent source) :=
  CPS1AddressedChemicalReaction.Material (NativeSpecies source current) NativeReaction

def oldCurrent (_source : Common before step raw) : CPS1Deformation.Source.Cursor frame :=
  cursor.native.current.old.current

def localSpecies (kind : FuelKind) : ChemicalKind :=
  match kind with | .atp => .atp | .bicarbonate => .bicarbonate

def firstFuel {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : FuelAt current := by
  let material := parent.products.dynamics.origin.material
  have vertices := source_token_vertices source current material.trace.selection.bond material.trace.selection.bondActual
  rw [material.products.token] at vertices
  have indexed := NativeCarbamoyl.source_fuel_occurrence source material.products.atp .atp leavingDescriptor vertices.2.1
  exact ⟨(.atp,material.products.atp),current.rawActual.symm ▸ indexed⟩

def bicarbonateFuel {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : FuelAt current :=
  ⟨(.bicarbonate,parent.products.dynamics.origin.material.products.bicarbonate),
    current.rawActual.symm ▸ parent.products.serial.sites.bicarbonateIndexed⟩

def secondFuel {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : FuelAt current :=
  ⟨(.atp,parent.products.serial.sites.atp),current.rawActual.symm ▸ parent.products.serial.sites.indexed⟩

def ammoniaSlot (_source : Common before step raw) : Fin (LiveStock cursor).length :=
  before.packet.source.ammonia.slot

def rawMaterial {source : Common before step raw} {current : NativeCurrent source}
    (_parent : ParentSource source current) (entry : FuelAt current) : NativeMaterial source current :=
  .raw cursor.native.current.ingress.atomic.source.nextBatch entry.1.2 (.fuel entry)

def liveMaterial {source : Common before step raw} {current : NativeCurrent source}
    (_parent : ParentSource source current) (slot : Fin (LiveStock cursor).length) : NativeMaterial source current :=
  .inherited (.live slot)

def activeMaterials (source : Common before step raw) (current : NativeCurrent source) : List (NativeMaterial source current) :=
  match actual : CPS1ReactiveField.heldDeformed cursor.native.current.old.current.stock with
  | none => []
  | some state => [.inherited (.active ⟨state,actual⟩)]

def parentStock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : List (NativeMaterial source current) :=
  activeMaterials source current ++ (List.finRange (LiveStock cursor).length).map (liveMaterial parent) ++
    current.materializedRaw.attach.map (rawMaterial parent)

def chosenParents {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : List (NativeMaterial source current) :=
  [rawMaterial parent (firstFuel parent),rawMaterial parent (bicarbonateFuel parent),
    liveMaterial parent (ammoniaSlot source),rawMaterial parent (secondFuel parent)]

def remainingParents {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : List (NativeMaterial source current) := by
  classical
  let afterFirst := (parentStock parent).erase (rawMaterial parent (firstFuel parent))
  let afterBicarbonate := afterFirst.erase (rawMaterial parent (bicarbonateFuel parent))
  exact (afterBicarbonate.erase (liveMaterial parent (ammoniaSlot source))).erase
    (rawMaterial parent (secondFuel parent))

def inputStock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : List (NativeMaterial source current) :=
  chosenParents parent ++ remainingParents parent

theorem chosen_parents_unique {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : (chosenParents parent).Nodup := by
  classical
  simp [chosenParents,rawMaterial,liveMaterial,firstFuel,bicarbonateFuel,secondFuel,
    CPS1AddressedChemicalReaction.Material.raw.injEq,NativeSpecies.fuel.injEq,Subtype.ext_iff,
    Ne.symm parent.products.serial.sites.fresh]

theorem chosen_parents_held {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : ∀ material ∈ chosenParents parent, material ∈ parentStock parent := by
  intro material held
  simp only [chosenParents,List.mem_cons,List.not_mem_nil,or_false] at held
  rcases held with rfl | rfl | rfl | rfl
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨firstFuel parent,List.mem_attach _ _,rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨bicarbonateFuel parent,List.mem_attach _ _,rfl⟩)
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
      ⟨ammoniaSlot source,List.mem_finRange _,rfl⟩))
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨secondFuel parent,List.mem_attach _ _,rfl⟩)

def eraseParents {α : Type} [DecidableEq α] (stock : List α) : List α → List α
  | [] => stock
  | parent :: rest => eraseParents (stock.erase parent) rest

theorem select_parents_perm {α : Type} [DecidableEq α] (stock chosen : List α) (unique : chosen.Nodup)
    (held : ∀ material ∈ chosen, material ∈ stock) : stock.Perm (chosen ++ eraseParents stock chosen) := by
  induction chosen generalizing stock with
  | nil => exact List.Perm.refl _
  | cons first rest ih =>
    have split := List.nodup_cons.mp unique
    have firstHeld := held first (by simp)
    have restHeld : ∀ material ∈ rest, material ∈ stock.erase first := by
      intro material member
      have different : material ≠ first := by
        intro same
        subst material
        exact split.1 member
      apply (List.mem_erase_of_ne different).mpr
      exact held material (by simp [member])
    exact (List.perm_cons_erase firstHeld).trans ((ih (stock.erase first) split.2 restHeld).cons first)

theorem input_is_whole_parent_stock {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : (parentStock parent).Perm (inputStock parent) := by
  classical
  exact select_parents_perm _ _ (chosen_parents_unique parent) (chosen_parents_held parent)

def reactants {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeReaction → List (NativeSpecies source current)
  | .phosphorylateBicarbonate => [.fuel (firstFuel parent),.fuel (bicarbonateFuel parent)]
  | .formCarbamate => [.live (ammoniaSlot source),.molecule .carboxyphosphate]
  | .phosphorylateCarbamate => [.fuel (secondFuel parent),.molecule .carbamate]

def products {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : NativeReaction → List (NativeSpecies source current)
  | .phosphorylateBicarbonate => [.molecule .adp,.molecule .carboxyphosphate]
  | .formCarbamate => [.molecule .carbamate,.molecule .phosphate,.molecule .proton]
  | .phosphorylateCarbamate =>
    if NativeCarbamoyl.classifyCP? parent.products.serial = some .carbamoylPhosphate then
      [.molecule .adp,.molecule .carbamoylPhosphate] else []

theorem last_products_generated {source : Common before step raw} {current : NativeCurrent source}
    (parent : ParentSource source current) : products parent .phosphorylateCarbamate =
      [.molecule .adp,.molecule .carbamoylPhosphate] := by
  rw [products,NativeCarbamoyl.source_cp_classified]
  rfl

end
end CPS1MaterialIncidence.NativePaidEvent
