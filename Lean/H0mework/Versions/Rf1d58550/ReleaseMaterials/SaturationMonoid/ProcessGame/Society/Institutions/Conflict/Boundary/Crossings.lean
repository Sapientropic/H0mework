import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Incidence
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Space.GeneratedSocialSpace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Source
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space

noncomputable section

universe u
variable {Party Good Port Technology Instrument Community : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Origin" => ProgrammeFace.Origin Party Good Port Technology Instrument
local notation "Point" => ProgrammeFace.Point Party Good Port Technology Instrument
local notation "Debit" => Row Party Good Port Technology Instrument

abbrev originalGame (law : Law) (origin : Origin) :=
  ProgrammeFace.game law (id : Origin → Origin) origin

abbrev activeSeed (_ : Origin) (_ : Point) (_ : Unit) : Prop := True
abbrev activeLineage (_ : Origin) := Unit

def queueSeed (law : Law) (origin : Origin) :
    SourceSeed (ProgrammeFace.occurrenceOf law (id : Origin → Origin)) Unit activeSeed origin :=
  ⟨(), .source origin, ProgrammeFace.source_mem_trace law origin, trivial⟩

/-- One queue unit per positive net debit address of the original execution
point. The existing programme game supplies every position. -/
def debitRate (law : Law) (origin : Origin) :
    SourceOwnedOccurrenceRateCompiler (originalGame law origin)
      Unit activeSeed activeLineage (fun _ _ => ()) (queueSeed law origin) where
  UnitAt := fun position => Fin (rowsAt law origin (stateAt (originalGame law origin) position)).length
  unitInventoryAt := fun position =>
    List.finRange (rowsAt law origin (stateAt (originalGame law origin) position)).length
  unitInventory_nodup := fun _ => List.nodup_finRange _
  raw_unit_mem := fun _ row => List.mem_finRange row
  seedAt := fun _ _ => ()
  seedIncidence := fun _ _ => trivial
  lineage_eq_focal := fun _ _ => rfl

def debitAt (law : Law) (origin : Origin) (position : (debitRate law origin).ExactQueueUnit) : Debit :=
  (rowsAt law origin position.state).get position.1.2

theorem debitAt_mem (law : Law) (origin : Origin) (position : (debitRate law origin).ExactQueueUnit) :
    debitAt law origin position ∈ rowsAt law origin position.state :=
  List.get_mem _ _

def partyIncidence (law : Law) (origin : Origin) (point : Point) (party : Party) : Prop :=
  ∃ row ∈ rowsAt law origin point, party = row.1.request.signer ∨ party = row.2.1

def boundaryIncidence (law : Law) (origin : Origin) (point : Point) (parties : Party × Party) : Prop :=
  ∃ row ∈ rowsAt law origin point, parties = (row.1.request.signer, row.2.1)

variable [DecidableEq Community]

/-- Positive net debits across distinct source communities activate M11.
The crossing flow is the exact original instruction and affected address. -/
def crossingCompiler (law : Law) (origin : Origin) (community : Party → Community) :
    SourceOwnedCrossingCompiler (debitRate law origin) where
  SiteSeed := Party
  SiteSeedAt := partyIncidence law
  SiteLineage := fun _ => Community
  siteLineageOf := fun _ seed => community seed.1
  originSeedAt := fun crossing => (debitAt law origin crossing).1.request.signer
  targetSeedAt := fun crossing => (debitAt law origin crossing).2.1
  originSeedIncidence := fun crossing =>
    ⟨debitAt law origin crossing, debitAt_mem law origin crossing, Or.inl rfl⟩
  targetSeedIncidence := fun crossing =>
    ⟨debitAt law origin crossing, debitAt_mem law origin crossing, Or.inr rfl⟩
  FlowPayloadAt := fun _ => Debit
  flowPayloadAt := debitAt law origin
  BoundarySeed := Party × Party
  BoundarySeedAt := boundaryIncidence law
  BoundaryLineage := fun _ => Community × Community
  boundaryLineageOf := fun _ seed => (community seed.1.1, community seed.1.2)
  BoundaryActiveAt := fun crossing => PLift
    (community (debitAt law origin crossing).1.request.signer ≠ community (debitAt law origin crossing).2.1)
  BoundaryInactiveAt := fun crossing => PLift
    (community (debitAt law origin crossing).1.request.signer = community (debitAt law origin crossing).2.1)
  classifyBoundary := fun crossing =>
    if same : community (debitAt law origin crossing).1.request.signer =
        community (debitAt law origin crossing).2.1
    then .inr ⟨same⟩ else .inl ⟨same⟩
  boundarySeedAt := fun crossing _ =>
    ((debitAt law origin crossing).1.request.signer, (debitAt law origin crossing).2.1)
  boundarySeedIncidence := fun crossing _ =>
    ⟨debitAt law origin crossing, debitAt_mem law origin crossing, rfl⟩

def sourceCrossings (law : Law) (origin : Origin) (community : Party → Community) :=
  SourceGeneratedSocialSpaceAt.generate (crossingCompiler law origin community)

theorem distinct_at_boundary (law : Law) (origin : Origin) (community : Party → Community)
    (boundary : (crossingCompiler law origin community).AnyBoundaryCertificate) :
    community (debitAt law origin boundary.crossing).1.request.signer ≠
      community (debitAt law origin boundary.crossing).2.1 :=
  boundary.proof.active.down

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
