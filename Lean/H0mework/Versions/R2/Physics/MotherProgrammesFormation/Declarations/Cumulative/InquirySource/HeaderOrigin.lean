import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.U7Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquirySource
open MotherInquiryU7Header
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}

/-- Fixed actual material outputs and their source equalities. The record
is a coverage witness, never a header input to the three graph factories. -/
structure HeaderOrigin (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) where
  addresses : Addresses (rank := rank) ⟨U7, calculus⟩
  demandMaterial : MotherArenaHigher.Material rank
  generatedDemand : U7ProducerCalculus N
  demand : MotherInquiryU7Demand.Presentation U7 generatedDemand
  demand_formed : MotherInquiryU7Demand.form addresses.obstruction demandMaterial = some generatedDemand
  eventMaterial : MotherArenaHigher.Material rank
  generatedSource : U7ActualSuccessorSource N demand.restrict
  event : MotherInquiryU7Events.Presentation demand.restrict
    (atU7 demand.restrict demand.restrict_eq calculus).2.source generatedSource
  event_formed :
    let codes := addressesAtU7 demand.restrict demand.restrict_eq calculus addresses
    MotherInquiryU7Events.form demand.restrict codes.obstruction codes.demand
      (fun support => (Function.Embedding.sigmaMk support).trans codes.entry) eventMaterial = some generatedSource
  compilerMaterial : MotherArenaHigher.Material rank
  generatedCalculus : U7ObstructionEvolutionCalculus N demand.restrict
  compiler_formed :
    let codes := addressesAtU7 demand.restrict demand.restrict_eq calculus addresses
    let compilerCodes := compilerAddresses codes event.restrict event.restrict_eq
    MotherInquiryU7.formCalculus event.restrict compilerCodes.event
      (fun point => (Function.Embedding.sigmaMk point).trans compilerCodes.disposition) compilerMaterial = some generatedCalculus
  recovered : (⟨demand.restrict, generatedCalculus⟩ : Header N) = ⟨U7, calculus⟩

def HeaderOrigin.read {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    (origin : HeaderOrigin (rank := rank) U7 calculus) : Header N :=
  let codes := addressesAtU7 origin.demand.restrict origin.demand.restrict_eq calculus origin.addresses
  let compilerCodes := compilerAddresses codes origin.event.restrict origin.event.restrict_eq
  let result := MotherInquiryU7.formCalculus origin.event.restrict compilerCodes.event
    (fun point => (Function.Embedding.sigmaMk point).trans compilerCodes.disposition) origin.compilerMaterial
  ⟨origin.demand.restrict, result.get (by
    have same : result = some origin.generatedCalculus := origin.compiler_formed
    rw [same]
    rfl)⟩

theorem HeaderOrigin.read_eq {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    (origin : HeaderOrigin (rank := rank) U7 calculus) : origin.read = ⟨U7, calculus⟩ :=
  (congrArg (Sigma.mk origin.demand.restrict)
    (Option.some.inj ((Option.some_get _).trans origin.compiler_formed))).trans origin.recovered

theorem header_origin_at (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
    (shared : AddressTotal ⟨U7, calculus⟩ ↪ MotherArenaHigher.Base rank) :
    Nonempty (HeaderOrigin (rank := rank) U7 calculus) := by
  let addresses := addressesOfTotal ⟨U7, calculus⟩ shared
  obtain ⟨demandMaterial, generatedDemand, demand, demandFormed, eventMaterial, generatedSource,
    event, eventFormed, compilerMaterial, generatedCalculus, compilerFormed, recovered⟩ :=
    header_at_rank U7 calculus addresses
  exact ⟨⟨addresses, demandMaterial, generatedDemand, demand, demandFormed,
    eventMaterial, generatedSource, event, eventFormed, compilerMaterial, generatedCalculus, compilerFormed, recovered⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquirySource
