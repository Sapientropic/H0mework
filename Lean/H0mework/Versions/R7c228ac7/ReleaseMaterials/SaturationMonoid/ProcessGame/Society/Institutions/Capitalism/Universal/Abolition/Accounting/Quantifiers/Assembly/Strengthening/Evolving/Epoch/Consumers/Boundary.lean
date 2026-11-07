import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
open Quantifiers.Joint.Consumers.Compact (seed grossClaim the_source_generates_its_own_sufficient_plan)
noncomputable section
attribute [local irreducible] Evolution.Ingress.Joint.Execution.Selected.items Evolution.Ingress.Joint.Execution.Selected.after
  Quantifiers.Joint.Planning.selected Quantifiers.Joint.Planning.actualNext

theorem source_control : current.control = Control.fromState (Actual.initial seed.input seed.depth seed.count) := by
  change (Source.initial original).control = _
  rw [Source.initial_source_phase_is_read_from_its_own_face]
  unfold Source.originalState Control.fromState
  have originalControl := Source.original_control_is_read_without_replaying_the_material_body
    original.input original.depth original.count original.prefixLimit original.renewalLimit original.oldPast original.actual.snapshot.past
  rw [originalControl.1,originalControl.2]
  rfl

theorem inherited_member : false ∈ Abolition.Root.Epoch.Interface.Actors.Census.parties seed.input seed.depth seed.count 0 0
    (Physical.Prefix.cursor []) := by decide +kernel

theorem live_members : current.members ≠ [] := by
  have member : false ∈ current.members := Abolition.Root.Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
    seed.input seed.depth seed.count 0 0 [] current.native.actual.snapshot false inherited_member
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

theorem source_code_boundary (raw origin : RawCurrent Bool Bool Unit Unit) (first : Bool) (rest : List Bool) :
    boundary (Public.Scope.checkInput seed.input) origin (first::rest) seed.depth seed.count 0 0
      ⟨raw,.seeking,(Actual.initial seed.input seed.depth seed.count).remaining⟩ := by
  cases first <;> (with_unfolding_all exact of_decide_eq_true rfl)

theorem the_actual_public_source_admits_the_new_code :
    boundary (Public.Scope.checkInput current.native.input)
      (Actual.origin current.native.input current.native.depth current.native.count) current.members current.native.depth
      current.native.count current.native.prefixLimit current.native.renewalLimit current.state := by
  unfold Current.state
  rw [source_control]
  cases originalMembers : current.members with
  | nil => exact (live_members originalMembers).elim
  | cons first rest => exact source_code_boundary current.raw _ first rest

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers
