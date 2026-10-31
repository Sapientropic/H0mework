import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.IssueTrace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.LawfulPrefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
theorem inventory_member_has_its_original_visit
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (origin : Financial.InstructionOrigin input) (member : origin ∈ Financial.inventoryAt input visit) :
    origin.visit = visit := by
  cases emission : input.emission? with
  | none =>
      simp only [Financial.inventoryAt,emission,Financial.administrativeInventoryAt] at member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      rfl
  | some emit =>
      simp only [Financial.inventoryAt,emission,List.mem_append] at member
      rcases member with administrative | traced
      · obtain ⟨index,rfl⟩ := List.mem_ofFn.mp administrative
        rfl
      · obtain ⟨index,rfl⟩ := List.mem_ofFn.mp traced
        rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
private theorem original_row_address_is_injective : Function.Injective (ProgrammeSource.rowAt input) := by
  intro first second same
  have inverse : ∀ index,ProgrammeSource.rowIndex input (ProgrammeSource.rowAt input index) = index := by
    intro index
    refine Fin.cases ?_ (fun remaining => ?_) index
    · rfl
    · refine Fin.cases ?_ (fun remaining => ?_) remaining <;> rfl
  exact (inverse first).symm.trans ((congrArg (ProgrammeSource.rowIndex input) same).trans (inverse second))

omit [DecidableEq Port] in
theorem an_actual_running_inventory_never_repeats_an_origin
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (raw : Source.Program.RawCurrent Party Good Technology Instrument)
    (past : List (Source.Program.RawCurrent Party Good Technology Instrument))
    (running : visit.current = .running raw past) :
    (Financial.inventoryAt input visit).Nodup := by
  rcases visit with ⟨current,history⟩
  cases running
  have administrative : (Financial.administrativeInventoryAt input ⟨_,history⟩).Nodup := by
    apply List.nodup_ofFn.mpr
    intro first second same
    apply original_row_address_is_injective input
    have rows := congrArg (fun origin : Financial.InstructionOrigin input => origin.item.1) same
    change ProgrammeSource.rowAt input first = ProgrammeSource.rowAt input second at rows
    exact rows
  have traced : (Financial.traceInventoryAt input ⟨_,history⟩).Nodup := by
    apply List.nodup_ofFn.mpr
    intro first second same
    apply Fin.ext
    exact Option.some.inj (congrArg (Financial.InstructionOrigin.traceIndex? (input := input)) same)
  cases emission : input.emission? with
  | none => simpa only [Financial.inventoryAt,emission] using administrative
  | some emit =>
      rw [Financial.inventoryAt,emission]
      apply List.nodup_append.mpr
      refine ⟨administrative,traced,?_⟩
      intro original old other new same
      obtain ⟨oldIndex,rfl⟩ := List.mem_ofFn.mp old
      obtain ⟨newIndex,rfl⟩ := List.mem_ofFn.mp new
      have incompatible := congrArg (Financial.InstructionOrigin.traceIndex? (input := input)) same
      cases incompatible

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source
