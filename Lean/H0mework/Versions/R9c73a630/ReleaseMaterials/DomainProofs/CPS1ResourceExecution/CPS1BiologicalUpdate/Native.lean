import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Selected
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Source

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1ReactiveSourceEntry CPS1LiveEditing
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
variable {frame : CPS1Recycling.Frame}

-- This decoder keeps the reached current's local chemical inventory, including the actual chain.
def liveLocal? : CPS1ReactiveField.LiveMaterial frame → Option (CPS1LocalChemicalExecution.Species frame)
  | .old (.retained (.retained (.retained (.retained (.retained (.retained (.retained (.retained localSpecies)))))))) =>
    some localSpecies
  | .reactive (.inherited localSpecies) => some localSpecies
  | _ => none

def liveLocal (current : CPS1ReactiveField.Occurrence frame) : CPS1LocalChemicalExecution.Stock frame :=
  (CPS1ReactiveField.liveStock current).filterMap liveLocal?

def actualGenePeptide (current : CPS1ReactiveField.Occurrence frame) : Option Peptide :=
  CPS1LiveEditing.readPeptide (CPS1LiveEditing.liveResources current)

inductive ProteinDamageRead
  | absentGenome
  | prematureStop (produced required : Nat)
  | fullLength
  deriving DecidableEq

def readProteinDamage (current : CPS1ReactiveField.Occurrence frame) : ProteinDamageRead :=
  match actualGenePeptide current with
  | none => .absentGenome
  | some peptide =>
    if peptide.2.length + 1 < Source.referenceProtein.length then
      .prematureStop (peptide.2.length + 1) Source.referenceProtein.length
    else .fullLength

structure MaterialRead (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  genome : Option Peptide
  genomeSource : genome = actualGenePeptide cursor.native.current
  chain : Option (CPS1LocalChemicalExecution.Chain frame)
  chainSource : chain = CPS1LocalChemicalExecution.Source.heldChain frame (liveLocal cursor.native.current)
  damage : ProteinDamageRead
  damageSource : damage = readProteinDamage cursor.native.current

def readMaterial (cursor : CPS1ReactiveNuclear.SourceCursor frame) : MaterialRead cursor :=
  ⟨actualGenePeptide cursor.native.current,rfl,
    CPS1LocalChemicalExecution.Source.heldChain frame (liveLocal cursor.native.current),rfl,
    readProteinDamage cursor.native.current,rfl⟩

def actualReachedCursor {entry : Entry frame} {depth : Nat} (outcome : BirthRun entry depth) :
    CPS1ReactiveNuclear.SourceCursor frame :=
  match outcome with
  | .residual cursor _ _ => cursor
  | .fired _ _ run => run.after.cursor

structure NativeBiosyntheticEvent (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat) where
  physicalEvent : PhysicalEvent before water raw path events feed physical
  outcome : BirthRun physicalEvent.entry depth
  oldRead : MaterialRead before
  nextRead : MaterialRead (actualReachedCursor outcome)
  releaseBefore : Nat
  releaseBeforeSource : releaseBefore = physicalEvent.seed.translation.available.count
    (.releasedPeptide physicalEvent.seed.translation.peptide)
  releaseAfter : Nat
  releaseAfterSource : releaseAfter = physicalEvent.seed.translation.native.stock.count
    (.releasedPeptide physicalEvent.seed.translation.peptide)
  newlyProduced : Nat
  newlyProducedSource : newlyProduced = releaseAfter - releaseBefore

def NativeBiosyntheticEvent.reached {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth) :
    CPS1ReactiveNuclear.SourceCursor event.physicalEvent.seed.translation.generatedFrame :=
  actualReachedCursor event.outcome

def nativeBiosyntheticEvent (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat)
    (source : PhysicalEvent before water raw path events feed physical)
    (outcome : BirthRun source.entry depth) : NativeBiosyntheticEvent before water raw path events feed physical depth :=
  let prior := source.seed.translation.available.count (.releasedPeptide source.seed.translation.peptide)
  let produced := source.seed.translation.native.stock.count (.releasedPeptide source.seed.translation.peptide)
  ⟨source,outcome,readMaterial before,readMaterial (actualReachedCursor outcome),
    prior,rfl,produced,rfl,produced-prior,rfl⟩

inductive BiosyntheticDisposition (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat)
  | sourceResidual (whole : WholeRun before water raw path events feed physical depth)
  | produced (event : NativeBiosyntheticEvent before water raw path events feed physical depth)

-- Only the actual returned event and its actual finite after are opened here.
def consumeWhole {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (whole : WholeRun (frame := frame) before water raw path events feed physical depth) :
    BiosyntheticDisposition before water raw path events feed physical depth := by
  rcases whole with ⟨original,originalSource,event,next,actual⟩
  cases event with
  | rejected originalEvent =>
    exact .sourceResidual ⟨original,originalSource,.rejected originalEvent,PUnit.unit,actual⟩
  | generated source =>
    exact .produced (nativeBiosyntheticEvent before water raw path events feed physical depth source next)

end
end CPS1BiologicalUpdate
