import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.U7Demand

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7Events
open MotherArenaNetwork MotherInquiryU7Demand
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} (U7 : U7ProducerCalculus N)
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev DemandPoint := MotherInquiryU7Demand.Total U7
abbrev Total (source : U7ActualSuccessorSource N U7) :=
  Σ point : DemandPoint U7, source.EventAt point.1.2 point.2

variable (obstructionCode : ObstructionPoint N ↪ MotherArenaHigher.Base rank)
    (demandCode : DemandPoint U7 ↪ MotherArenaHigher.Base rank)
    (entryCode : ∀ support, OpenResponsibilityAt N support ↪ MotherArenaHigher.Base rank)

abbrev Event (base : M) (point : DemandPoint U7) := {code : B // r2 base 0 (demandCode point) code}
abbrev EventPoint (base : M) := Σ point : DemandPoint U7, Event U7 demandCode base point

def eventAddress (base : M) : EventPoint U7 demandCode base ↪ B :=
  MotherArenaObligation.sigmaEmbedding demandCode (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)

def GeneratedDemands (base : M) : Prop := ∀ (point : DemandPoint U7),
  Event U7 demandCode base point → point.2 = U7.generateDemand point.1.2

def assemble (base : M) (generated : GeneratedDemands U7 demandCode base)
    (emit : ∀ point : ObstructionPoint N, Event U7 demandCode base ⟨point, U7.generateDemand point.2⟩)
    (entry : ∀ point : EventPoint U7 demandCode base, OpenResponsibilityAt N point.1.1.1) :
    U7ActualSuccessorSource N U7 where
  EventAt := fun {support} obstruction demand => Event U7 demandCode base ⟨⟨support, obstruction⟩, demand⟩
  emit := fun {support} obstruction => emit ⟨support, obstruction⟩
  demandGeneratedAt := fun {support} {obstruction} {demand} event =>
    Eq.mp (congrArg (SourceGeneratedU7DemandAt U7 obstruction)
      (generated ⟨⟨support, obstruction⟩, demand⟩ event).symm) (SourceGeneratedU7DemandAt.canonical obstruction)
  demandEntryAt := fun {support} {obstruction} {demand} event => entry ⟨⟨⟨support, obstruction⟩, demand⟩, event⟩

def formParts (base emitter entries : M) : Option (U7ActualSuccessorSource N U7) :=
  if generated : GeneratedDemands U7 demandCode base then
    (MotherArenaReceipts.NativeSection.form obstructionCode
      (fun point => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
        Event U7 demandCode base ⟨point, U7.generateDemand point.2⟩ ↪ B)) emitter).bind (fun emit =>
      (MotherArenaReceipts.NativeSection.form (eventAddress U7 demandCode base)
        (fun point => entryCode point.1.1.1) entries).map (assemble U7 demandCode base generated emit))
  else none

/-- Full demand-indexed event fibers, canonical emission and the entire
world-ledger entry program are read from source materials. -/
def form (material : M) : Option (U7ActualSuccessorSource N U7) :=
  let first := MotherArenaHigher.split rank material
  let last := MotherArenaHigher.split rank first.2
  formParts U7 obstructionCode demandCode entryCode first.1 last.1 last.2

structure Presentation (old generated : U7ActualSuccessorSource N U7) where
  event : ∀ support (obstruction : N.ObstructionAt support) (demand : U7.DemandAt obstruction),
    old.EventAt obstruction demand ≃ generated.EventAt obstruction demand
  emit_eq : ∀ support (obstruction : N.ObstructionAt support),
    generated.emit obstruction = event support obstruction (U7.generateDemand obstruction) (old.emit obstruction)
  entry_eq : ∀ support (obstruction : N.ObstructionAt support) (demand : U7.DemandAt obstruction)
    (value : old.EventAt obstruction demand),
    generated.demandEntryAt (event support obstruction demand value) = old.demandEntryAt value

namespace Presentation
variable {U7} {old generated : U7ActualSuccessorSource N U7} (p : Presentation U7 old generated)

def restrict : U7ActualSuccessorSource N U7 where
  EventAt := old.EventAt
  emit := fun {support} obstruction => (p.event support obstruction (U7.generateDemand obstruction)).symm (generated.emit obstruction)
  demandGeneratedAt := fun {support} {obstruction} {demand} event =>
    generated.demandGeneratedAt (p.event support obstruction demand event)
  demandEntryAt := fun {support} {obstruction} {demand} event =>
    generated.demandEntryAt (p.event support obstruction demand event)

theorem restrict_eq : p.restrict = old := by
  have emitted : (fun {support} (obstruction : N.ObstructionAt support) =>
      (p.event support obstruction (U7.generateDemand obstruction)).symm (generated.emit obstruction)) = @old.emit := by
    funext support obstruction
    exact (congrArg (p.event support obstruction (U7.generateDemand obstruction)).symm (p.emit_eq support obstruction)).trans
      ((p.event support obstruction (U7.generateDemand obstruction)).symm_apply_apply _)
  have authority : (fun {support} {obstruction : N.ObstructionAt support} {demand : U7.DemandAt obstruction}
      (event : old.EventAt obstruction demand) => generated.demandGeneratedAt (p.event support obstruction demand event)) =
        @old.demandGeneratedAt := by
    funext support obstruction demand event
    exact Subsingleton.elim _ _
  have entry : (fun {support} {obstruction : N.ObstructionAt support} {demand : U7.DemandAt obstruction}
      (event : old.EventAt obstruction demand) => generated.demandEntryAt (p.event support obstruction demand event)) =
        @old.demandEntryAt := by
    funext support obstruction demand event
    exact p.entry_eq support obstruction demand event
  unfold restrict
  rw [emitted, authority, entry]

end Presentation

theorem every_at_rank (old : U7ActualSuccessorSource N U7) (code : Total U7 old ↪ B) :
    ∃ material : M, ∃ generated : U7ActualSuccessorSource N U7,
      form U7 obstructionCode demandCode entryCode material = some generated ∧ Nonempty (Presentation U7 old generated) := by
  obtain ⟨base, relation⟩ := MotherArenaNetwork.every_binary_graph (rank := rank) 0
    (fun context output => ∃ point : DemandPoint U7, ∃ event : old.EventAt point.1.2 point.2,
      demandCode point = context ∧ code ⟨point, event⟩ = output)
  have at_fiber (point : DemandPoint U7) (output : B) :
      r2 base 0 (demandCode point) output ↔ ∃ event : old.EventAt point.1.2 point.2, code ⟨point, event⟩ = output := by
    rw [relation]
    constructor
    · rintro ⟨other, event, same, selected⟩
      have equal := demandCode.injective same
      cases equal
      exact ⟨event, selected⟩
    · rintro ⟨event, selected⟩
      exact ⟨point, event, rfl, selected⟩
  let fibers : ∀ point : DemandPoint U7, old.EventAt point.1.2 point.2 ≃ Event U7 demandCode base point :=
    fun point => MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk point).trans code)
      (r2 base 0 (demandCode point)) (at_fiber point)
  have generated : GeneratedDemands U7 demandCode base := by
    intro point event
    exact SourceGeneratedU7DemandAt.payload_eq_generated (old.demandGeneratedAt ((fibers point).symm event))
  let emit : ∀ point : ObstructionPoint N, Event U7 demandCode base ⟨point, U7.generateDemand point.2⟩ :=
    fun point => fibers ⟨point, U7.generateDemand point.2⟩ (old.emit point.2)
  let entry : ∀ point : EventPoint U7 demandCode base, OpenResponsibilityAt N point.1.1.1 :=
    fun point => old.demandEntryAt ((fibers point.1).symm point.2)
  obtain ⟨emitter, emitFormed⟩ := MotherArenaReceipts.NativeSection.every_section obstructionCode
    (fun point => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
      Event U7 demandCode base ⟨point, U7.generateDemand point.2⟩ ↪ B)) emit
  obtain ⟨entries, entryFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (eventAddress U7 demandCode base) (fun point => entryCode point.1.1.1) entry
  refine ⟨MotherArenaHigher.pack rank (base, MotherArenaHigher.pack rank (emitter, entries)),
    assemble U7 demandCode base generated emit entry, ?_, ⟨{
      event := fun support obstruction demand => fibers ⟨⟨support, obstruction⟩, demand⟩
      emit_eq := fun _ _ => rfl
      entry_eq := fun support obstruction demand event =>
        congrArg old.demandEntryAt ((fibers ⟨⟨support, obstruction⟩, demand⟩).symm_apply_apply event) }⟩⟩
  unfold form
  rw [MotherArenaHigher.split_pack]
  dsimp only
  rw [MotherArenaHigher.split_pack]
  dsimp only
  rw [formParts, dif_pos generated, emitFormed, Option.bind_some, entryFormed]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7Events
