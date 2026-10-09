import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Continuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Release

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1ReactiveSourceEntry CPS1LiveEditing
variable {frame : CPS1Recycling.Frame}
variable {before : CPS1ReactiveNuclear.SourceCursor frame}
variable {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
variable {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
variable {physical : PhysicalRaw} {depth : Nat}

def PrematureStop (read : ProteinDamageRead) : Prop :=
  match read with
  | .prematureStop _ _ => True
  | _ => False
instance (read : ProteinDamageRead) : Decidable (PrematureStop read) := by
  cases read <;> unfold PrematureStop <;> infer_instance

structure RenewedBiosynthesis
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth)
    (supply : ContinuationRaw) where
  continuation : ContinuedBiosynthesis event supply
  returned : NativeBiosyntheticEvent event.reached supply.water supply.translation
    supply.path supply.recycling supply.recycleFeed supply.physical supply.depth
  selected : consumeWhole continuation.next = .produced returned
  priorDamage : PrematureStop (readProteinDamage before.native.current)
  priorNative : event.physicalEvent.seed.translation.native.missing = none
  priorBirth : event.newlyProduced = 1
  repairedRead : readProteinDamage event.reached.native.current = .fullLength
  sameTemplate : returned.physicalEvent.seed.translation.coding = event.physicalEvent.seed.translation.coding
  nextNative : returned.physicalEvent.seed.translation.native.missing = none
  nextBirth : returned.newlyProduced = 1
  nextRead : readProteinDamage returned.reached.native.current = .fullLength

inductive RenewalFailure
  | priorNativeCut (missing : Option Species)
  | noPrematureStop (observed : ProteinDamageRead)
  | genomicReadResidual (observed : ProteinDamageRead)
  | nextSourceResidual
  | changedTemplate
  | nextNativeCut (missing : Option Species)
  | nextGenomicResidual (observed : ProteinDamageRead)

inductive RenewalDisposition
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth)
    (supply : ContinuationRaw)
  | residual (continuation : ContinuedBiosynthesis event supply) (failure : RenewalFailure)
  | renewed (update : RenewedBiosynthesis event supply)

private theorem actual_birth_one
    {original : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (event : NativeBiosyntheticEvent original water raw path events feed physical depth)
    (complete : event.physicalEvent.seed.translation.native.missing = none) : event.newlyProduced = 1 := by
  rw [biosynthetic_birth_credit]
  exact (translation_release_is_new _ _ _ event.physicalEvent.seed.translation complete).2.1

def renewBiosynthesis
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth)
    (supply : ContinuationRaw) : RenewalDisposition event supply :=
  let continuation := continueBiosynthesis event supply
  if priorNative : event.physicalEvent.seed.translation.native.missing = none then
    if priorDamage : PrematureStop (readProteinDamage before.native.current) then
      if repaired : readProteinDamage event.reached.native.current = .fullLength then
        match selected : consumeWhole continuation.next with
        | .sourceResidual _ => .residual continuation .nextSourceResidual
        | .produced returned =>
          if sameTemplate : returned.physicalEvent.seed.translation.coding = event.physicalEvent.seed.translation.coding then
            if nextNative : returned.physicalEvent.seed.translation.native.missing = none then
              if nextRead : readProteinDamage returned.reached.native.current = .fullLength then
                .renewed ⟨continuation,returned,selected,priorDamage,priorNative,
                  actual_birth_one event priorNative,repaired,sameTemplate,nextNative,
                  actual_birth_one returned nextNative,nextRead⟩
              else .residual continuation (.nextGenomicResidual (readProteinDamage returned.reached.native.current))
            else .residual continuation (.nextNativeCut returned.physicalEvent.seed.translation.native.missing)
          else .residual continuation .changedTemplate
      else .residual continuation (.genomicReadResidual (readProteinDamage event.reached.native.current))
    else .residual continuation (.noPrematureStop (readProteinDamage before.native.current))
  else .residual continuation (.priorNativeCut event.physicalEvent.seed.translation.native.missing)

inductive BiologicalDisposition (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat) (supply : ContinuationRaw)
  | originalResidual (whole : WholeRun before water raw path events feed physical depth)
      (readout : BiosyntheticDisposition before water raw path events feed physical depth)
  | localUpdate (whole : WholeRun before water raw path events feed physical depth)
      (event : NativeBiosyntheticEvent before water raw path events feed physical depth)
      (selected : consumeWhole whole = .produced event) (result : RenewalDisposition event supply)

def biologicalUpdate (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat) (supply : ContinuationRaw) :
    BiologicalDisposition before water raw path events feed physical depth supply :=
  let whole := executeWhole before water raw path events feed physical depth
  match selected : consumeWhole whole with
  | .sourceResidual source => .originalResidual whole (.sourceResidual source)
  | .produced event => .localUpdate whole event selected (renewBiosynthesis event supply)

end
end CPS1BiologicalUpdate
