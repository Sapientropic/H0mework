import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.ProperKernel
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.CompleteWord

/-! The source's finite local action grammar supplies separability witnesses.
The generated family is checked at the original access phase.  Failure to
discover one leaves excluded original ports unresolved, never independent. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (localAttempts : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)

private def firstSome {α β : Type u} (produce : α → Option β) : List α → Option β
  | [] => none
  | head :: tail => match produce head with
    | some value => some value
    | none => firstSome produce tail

/-- This search generates a dependency kernel from actual occurrence items;
it does not accept a candidate or classification certificate as input. -/
def dependencyAt (access : AccessProposal law current word) :
    Option (CapitalRelationKernel law current word) :=
  if access.Checks law current word then
    firstSome (fun reciprocity =>
      firstSome (fun disposal => Kernel.compile law current word ⟨access, reciprocity, disposal⟩)
        (Discovery.disposals law current word access))
      (Discovery.reciprocities law current word access)
  else none

structure SourceCapital where
  private mk ::
  dependency : CapitalRelationKernel law current word
  quotation : { request : Request Party Good Port Technology Instrument //
    request ∈ localAttempts dependency.proposal.access.access.val.before }
  proper : ProperCapitalKernel law current word
  generated : compileProper law current word dependency
    dependency.proposal.access.access quotation.val = some proper

def sourceCapital (dependency : CapitalRelationKernel law current word)
    (quotation : { request : Request Party Good Port Technology Instrument //
      request ∈ localAttempts dependency.proposal.access.access.val.before }) :
    Option (SourceCapital law current word localAttempts) :=
  match generated : compileProper law current word dependency
      dependency.proposal.access.access quotation.val with
  | none => none
  | some proper => some ⟨dependency, quotation, proper, generated⟩

def sourceCapitalAt (access : AccessProposal law current word) :
    Option (SourceCapital law current word localAttempts) :=
  match dependencyAt law current word access with
  | none => none
  | some dependency => firstSome (sourceCapital law current word localAttempts dependency)
      (localAttempts dependency.proposal.access.access.val.before).attach

def discovered : List (SourceCapital law current word localAttempts) :=
  (Discovery.accesses law current word).filterMap (sourceCapitalAt law current word localAttempts)

/-- Relation membership is read at this actual intermediate phase.  A port
that has become shared is not retained merely because its old name occurs. -/
def generatedFamily (item : OriginalItem law current word) : List Port :=
  (discovered law current word localAttempts).filterMap (fun capital =>
    if PrivatePhase law item.val.before capital.dependency.proposal.access.port
        capital.dependency.proposal.access.recipient then
      some capital.dependency.proposal.access.port
    else none)

namespace SourceCapital
variable (capital : SourceCapital law current word localAttempts)

theorem proper_dependency_exact : capital.proper.dependency = capital.dependency :=
  compileProper_dependency law current word _ _ _ _ capital.generated

theorem original_access_and_source_quotation :
    law.Valid capital.dependency.proposal.access.access.val.before
      capital.dependency.proposal.access.access.val.request ∧
    capital.dependency.proposal.access.port ∈
      law.requiredPorts capital.dependency.proposal.access.access.val.before
        capital.dependency.proposal.access.access.val.request ∧
    capital.quotation.val ∈ localAttempts capital.dependency.proposal.access.access.val.before :=
  ⟨capital.dependency.checked.1.1, capital.dependency.checked.1.2.1, capital.quotation.property⟩

end SourceCapital

theorem generatedFamily_original_provenance (item : OriginalItem law current word) (port : Port)
    (member : port ∈ generatedFamily law current word localAttempts item) :
    ∃ capital ∈ discovered law current word localAttempts,
      capital.dependency.proposal.access.port = port ∧
      PrivatePhase law item.val.before port capital.dependency.proposal.access.recipient := by
  obtain ⟨capital, original, found⟩ := List.mem_filterMap.mp member
  split at found
  · rename_i privatePhase
    exact ⟨capital, original, Option.some.inj found,
      (Option.some.inj found) ▸ privatePhase⟩
  · contradiction

theorem fixed_personal_port_not_in_generatedFamily (port : Port) (actor : Party)
    (fixed : ∀ technology, law.controller technology port = actor)
    (item : OriginalItem law current word) :
    port ∉ generatedFamily law current word localAttempts item := by
  intro member
  obtain ⟨capital, _original, samePort, _phase⟩ :=
    generatedFamily_original_provenance law current word localAttempts item port member
  exact fixed_personal_authority_cannot_be_proper_capital law current word port actor fixed
    capital.proper ((congrArg (fun kernel => kernel.proposal.access.port)
      (capital.proper_dependency_exact law current word localAttempts)).trans samePort)

theorem unclassified_exclusion_retains_original_item (group : List Party)
    (item : OriginalItem law current word) (port : Port)
    (required : port ∈ law.requiredPorts item.val.before item.val.request)
    (absent : port ∉ generatedFamily law current word localAttempts item)
    (person : Party) (inside : person ∈ group)
    (excluded : law.allowed item.val.before.technology port person = false) :
    UnresolvedAt law current word (generatedFamily law current word localAttempts) group item := by
  right
  refine ⟨port, required, absent, ?_⟩
  intro shared
  have allowed := shared person inside
  exact Bool.noConfusion (allowed.symm.trans excluded)

#print axioms discovered
#print axioms generatedFamily_original_provenance
#print axioms fixed_personal_port_not_in_generatedFamily
#print axioms unclassified_exclusion_retains_original_item

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority
