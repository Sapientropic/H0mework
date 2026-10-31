import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Core
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Detector

/-! Source discovery tests the actual-appropriation condition before it
selects a dependency result.  An earlier potential disposal cannot mask a
later performed consumption, paid investment or output-retention witness. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

private def firstSome {α β : Type u} (f : α → Option β) : List α → Option β
  | [] => none
  | head :: tail => match f head with
    | some found => some found
    | none => firstSome f tail

def evidenceCandidates (access : AccessProposal law current word) : List (Evidence law current word) :=
  (law.rawItems current word).attach.flatMap (fun position =>
    match position.val.request.operation with
    | .use _ goods _ => [.consumption position] ++ goods.filterMap (fun lot =>
        (controlledRouteBetween law current word access.port access.recipient
          (access.accessHolder, access.accessGood)
          (law.controller position.val.before.technology access.port, lot.1)
          (access.access.val.index + 1) position.val.index).map (fun route =>
            .routedConsumption position lot.1 route))
    | .revise _ target =>
        (law.technique target access.accessHolder).outputs.map (fun lot => .investment position lot.1)
    | _ => []) ++ [.retention] ++
      (Financial.returnPaths law current word).map Evidence.financialReturn

def sourceAt (access : AccessProposal law current word) : Option (Witness law current word) :=
  if access.Checks law current word ∧ access.mode = .acquired then
    firstSome (fun evidence =>
      if evidenceChecks law current word access evidence then
        firstSome (fun reciprocity =>
          firstSome (fun disposal =>
            if disposal.allocations = [] then
              compileProposal law current word ⟨access, reciprocity, disposal⟩ evidence
            else none) (Discovery.disposals law current word access))
          (Discovery.reciprocities law current word access)
      else none) (evidenceCandidates law current word access)
  else none

def discovered : List (Witness law current word) :=
  (Discovery.accesses law current word).filterMap (sourceAt law current word)

def familyAt (item : OriginalItem law current word) : List Port :=
  (discovered law current word).filterMap (fun witness =>
    if PrivatePhase law item.val.before witness.dependency.proposal.access.port
        witness.dependency.proposal.access.recipient then
      some witness.dependency.proposal.access.port
    else none)

theorem discovered_is_source_checked (witness : Witness law current word)
    (member : witness ∈ discovered law current word) :
    ∃ access ∈ Discovery.accesses law current word,
      sourceAt law current word access = some witness := List.mem_filterMap.mp member

theorem familyAt_has_original_witness (item : OriginalItem law current word) (port : Port)
    (member : port ∈ familyAt law current word item) :
    ∃ witness ∈ discovered law current word,
      witness.dependency.proposal.access.port = port ∧
      PrivatePhase law item.val.before port witness.dependency.proposal.access.recipient := by
  obtain ⟨witness, source, found⟩ := List.mem_filterMap.mp member
  split at found
  · rename_i phase
    exact ⟨witness, source, Option.some.inj found, (Option.some.inj found) ▸ phase⟩
  · cases found

theorem discovered_generates_actual_control (witness : Witness law current word)
    (member : witness ∈ discovered law current word) :
    Nonempty (ControlUse law current word (familyAt law current word)) := by
  let access := witness.dependency.proposal.access
  refine ⟨⟨access.access, witness.dependency.checked.1.1, access.port,
    witness.dependency.checked.1.2.1, ?_⟩⟩
  exact List.mem_filterMap.mpr ⟨witness, member,
    if_pos witness.dependency.checked.1.2.2.1⟩

#print axioms discovered
#print axioms familyAt_has_original_witness

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus
