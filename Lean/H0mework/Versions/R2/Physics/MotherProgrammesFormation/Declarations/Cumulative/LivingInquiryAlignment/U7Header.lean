import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.U7Events

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7Header
open MotherInquiryU7Demand
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev Header (N : WorldRelationNetwork.{0}) := Σ U7 : U7ProducerCalculus N, U7ObstructionEvolutionCalculus N U7

structure Addresses (header : Header N) where
  obstruction : ObstructionPoint N ↪ B
  demand : MotherInquiryU7Demand.Total header.1 ↪ B
  event : MotherInquiryU7Events.Total header.1 header.2.source ↪ B
  entry : (Σ support, OpenResponsibilityAt N support) ↪ B
  compilerEvent : MotherInquiryU7.EventTotal header.2.source ↪ B
  disposition : (Σ point, MotherInquiryU7.DispositionAt header.2.source point) ↪ B

def atU7 {old : U7ProducerCalculus N} (actual : U7ProducerCalculus N) (same : actual = old)
    (calculus : U7ObstructionEvolutionCalculus N old) : Header N :=
  ⟨actual, Equiv.cast (congrArg (U7ObstructionEvolutionCalculus N) same.symm) calculus⟩

theorem atU7_eq {old : U7ProducerCalculus N} (actual : U7ProducerCalculus N) (same : actual = old)
    (calculus : U7ObstructionEvolutionCalculus N old) : atU7 actual same calculus = ⟨old, calculus⟩ := by
  cases same
  rfl

def addressesAtU7 {old : U7ProducerCalculus N} (actual : U7ProducerCalculus N) (same : actual = old)
    (calculus : U7ObstructionEvolutionCalculus N old) (addresses : Addresses (rank := rank) ⟨old, calculus⟩) :
    Addresses (rank := rank) (atU7 actual same calculus) :=
  Equiv.cast (congrArg (Addresses (rank := rank)) (atU7_eq actual same calculus).symm) addresses

def atSource {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    (actual : U7ActualSuccessorSource N U7) (same : actual = calculus.source) : U7ObstructionEvolutionCalculus N U7 :=
  MotherInquiryU7.assemble actual
    (Equiv.cast (congrArg MotherInquiryU7.CompilationSection same.symm)
      (fun point => calculus.compile point.2.2.2))

theorem atSource_eq {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    (actual : U7ActualSuccessorSource N U7) (same : actual = calculus.source) :
    atSource calculus actual same = calculus := by
  cases same
  rfl

structure CompilerAddresses {U7 : U7ProducerCalculus N} (source : U7ActualSuccessorSource N U7) where
  event : MotherInquiryU7.EventTotal source ↪ B
  disposition : (Σ point, MotherInquiryU7.DispositionAt source point) ↪ B

def compilerAddresses {header : Header N} (addresses : Addresses (rank := rank) header)
    (actual : U7ActualSuccessorSource N header.1) (same : actual = header.2.source) :
    CompilerAddresses (rank := rank) actual :=
  Equiv.cast (congrArg (CompilerAddresses (rank := rank)) same.symm)
    ⟨addresses.compilerEvent, addresses.disposition⟩

/-- Complete U7 header recovery at one previously selected sufficient rank.
Demand and event fields are actual graph types. Both emitters, ledger entries
and every native compile value are read from actual mother materials. -/
abbrev FormationAt (old : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N old)
    (addresses : Addresses (rank := rank) ⟨old, calculus⟩) : Prop :=
    ∃ demandMaterial : M, ∃ generatedDemand : U7ProducerCalculus N,
    ∃ demandPresentation : MotherInquiryU7Demand.Presentation old generatedDemand,
      MotherInquiryU7Demand.form addresses.obstruction demandMaterial = some generatedDemand ∧
      let target := atU7 demandPresentation.restrict demandPresentation.restrict_eq calculus
      let codes := addressesAtU7 demandPresentation.restrict demandPresentation.restrict_eq calculus addresses
      ∃ eventMaterial : M, ∃ generatedSource : U7ActualSuccessorSource N target.1,
      ∃ eventPresentation : MotherInquiryU7Events.Presentation target.1 target.2.source generatedSource,
        MotherInquiryU7Events.form target.1 codes.obstruction codes.demand
          (fun support => (Function.Embedding.sigmaMk support).trans codes.entry) eventMaterial = some generatedSource ∧
        let compilerCodes := compilerAddresses codes eventPresentation.restrict eventPresentation.restrict_eq
        ∃ compilerMaterial : M, ∃ actualCalculus : U7ObstructionEvolutionCalculus N target.1,
          MotherInquiryU7.formCalculus eventPresentation.restrict compilerCodes.event
            (fun point => (Function.Embedding.sigmaMk point).trans compilerCodes.disposition) compilerMaterial = some actualCalculus ∧
          (⟨demandPresentation.restrict, actualCalculus⟩ : Header N) = ⟨old, calculus⟩

theorem header_at_rank (old : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N old)
    (addresses : Addresses (rank := rank) ⟨old, calculus⟩) : FormationAt old calculus addresses := by
  obtain ⟨demandMaterial, generatedDemand, demandFormed, ⟨demandPresentation⟩⟩ :=
    MotherInquiryU7Demand.every_at_rank addresses.obstruction old addresses.demand
  let target := atU7 demandPresentation.restrict demandPresentation.restrict_eq calculus
  let codes := addressesAtU7 demandPresentation.restrict demandPresentation.restrict_eq calculus addresses
  obtain ⟨eventMaterial, generatedSource, eventFormed, ⟨eventPresentation⟩⟩ :=
    MotherInquiryU7Events.every_at_rank target.1 codes.obstruction codes.demand
      (fun support => (Function.Embedding.sigmaMk support).trans codes.entry) target.2.source codes.event
  let compilerCodes := compilerAddresses codes eventPresentation.restrict eventPresentation.restrict_eq
  let targetCompiler := atSource target.2 eventPresentation.restrict eventPresentation.restrict_eq
  obtain ⟨compilerMaterial, compilerFormed⟩ := MotherInquiryU7.every_calculus_at_rank targetCompiler
    compilerCodes.event (fun point => (Function.Embedding.sigmaMk point).trans compilerCodes.disposition)
  refine ⟨demandMaterial, generatedDemand, demandPresentation, demandFormed,
    eventMaterial, generatedSource, eventPresentation, eventFormed,
    compilerMaterial, targetCompiler, compilerFormed, ?_⟩
  exact (congrArg (Sigma.mk demandPresentation.restrict)
    (atSource_eq target.2 eventPresentation.restrict eventPresentation.restrict_eq)).trans
      (atU7_eq demandPresentation.restrict demandPresentation.restrict_eq calculus)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7Header
