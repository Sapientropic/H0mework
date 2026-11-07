import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Resolution
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Consumers

open Source.Program PublicFunction PublicFunction.Mandate
open OutstandingSource.History.NativeService
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

noncomputable section

abbrev original := Lifecycle.Source.bound

def closingWord : List Source.Action := Id.run do
  let current := target original [] []
  let proposal := request Source.scope current false (.propose true)
  let offered := Source.law.step current proposal
  let acceptance := request Source.scope offered true .accept
  let held := Source.law.step offered acceptance
  let served := Source.law.step (Source.law.step held Source.necessity) Source.maintenance
  return [proposal, acceptance, Source.necessity, Source.maintenance,
    request Source.scope served true .exit]

private abbrev geometry := serviceGeometry original [] [closingWord]

private def necessityEdge : original.source.Slot × Fin (originalInventory original [] [closingWord]).length :=
  (⟨0, by decide⟩, ⟨9, by decide +kernel⟩)

private def maintenanceEdge : original.source.Slot × Fin (originalInventory original [] [closingWord]).length :=
  (⟨1, by decide⟩, ⟨10, by decide +kernel⟩)

private theorem admittedEdge (edge : original.source.Slot × Fin (originalInventory original [] [closingWord]).length)
    (left : edge.1 ∈ geometry.leftCarrier) (valid : geometry.Feasible edge.1 edge.2) :
    edge ∈ geometry.edgeCarrier :=
  (geometry.mem_edgeCarrier_iff edge).mpr ⟨left, Finset.mem_univ _, valid⟩

private theorem two_actual_debits_cover_the_original_mandate :
    geometry.maximumMatchingCapacity = geometry.leftCarrier.card := by
  have necessity : necessityEdge ∈ geometry.edgeCarrier := by
    apply admittedEdge
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide +kernel⟩
    · change Source.task.earliest ≤ ((originalInventory original [] [closingWord]).get necessityEdge.2).before.clock ∧
        Source.law.Valid ((originalInventory original [] [closingWord]).get necessityEdge.2).before
          ((originalInventory original [] [closingWord]).get necessityEdge.2).request ∧
        Exit.Necessity.UseMatches ((originalInventory original [] [closingWord]).get necessityEdge.2).request.operation
          (Source.task.slots.get necessityEdge.1).bearer (Source.task.slots.get necessityEdge.1).goods
          (Source.task.slots.get necessityEdge.1).purpose
      refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
  have maintenance : maintenanceEdge ∈ geometry.edgeCarrier := by
    apply admittedEdge
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide +kernel⟩
    · change Source.task.earliest ≤ ((originalInventory original [] [closingWord]).get maintenanceEdge.2).before.clock ∧
        Source.law.Valid ((originalInventory original [] [closingWord]).get maintenanceEdge.2).before
          ((originalInventory original [] [closingWord]).get maintenanceEdge.2).request ∧
        Exit.Necessity.UseMatches ((originalInventory original [] [closingWord]).get maintenanceEdge.2).request.operation
          (Source.task.slots.get maintenanceEdge.1).bearer (Source.task.slots.get maintenanceEdge.1).goods
          (Source.task.slots.get maintenanceEdge.1).purpose
      refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
  let both := ({necessityEdge, maintenanceEdge} : Finset _)
  have listed : both ∈ geometry.matchings := by
    classical
    unfold CanonicalBipartiteFeasibility.matchings
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro edge inside
      rcases Finset.mem_insert.mp inside with rfl | tail
      · exact necessity
      · rw [Finset.mem_singleton] at tail
        exact tail ▸ maintenance
    · constructor
      · intro first inFirst second inSecond same
        change first ∈ both at inFirst
        change second ∈ both at inSecond
        simp only [both, Finset.mem_insert, Finset.mem_singleton] at inFirst inSecond
        rcases inFirst with rfl | rfl <;> rcases inSecond with rfl | rfl <;> first
        | rfl
        | exact ((show necessityEdge.1 ≠ maintenanceEdge.1 by decide) same).elim
        | exact ((show necessityEdge.1 ≠ maintenanceEdge.1 by decide) same.symm).elim
      · intro first inFirst second inSecond same
        change first ∈ both at inFirst
        change second ∈ both at inSecond
        simp only [both, Finset.mem_insert, Finset.mem_singleton] at inFirst inSecond
        rcases inFirst with rfl | rfl <;> rcases inSecond with rfl | rfl <;> first
        | rfl
        | exact ((show necessityEdge.2 ≠ maintenanceEdge.2 by decide) same).elim
        | exact ((show necessityEdge.2 ≠ maintenanceEdge.2 by decide) same.symm).elim
  apply le_antisymm geometry.maximumMatchingCapacity_le_left
  have covers : both.card = geometry.leftCarrier.card := by decide +kernel
  exact covers ▸ Finset.le_sup (f := Finset.card) listed

theorem original_service_and_release_are_actually_paid : PaidAt original [] [closingWord] where
  slots := by
    intro slot
    apply ((serviceThread original [] [closingWord] slot).native_terminal_iff_recorded original.source).mpr
    refine ⟨2, ?_⟩
    change (frameAt original.source [closingWord] 3).payments slot = some 2
    have found : ∀ slot : original.source.Slot, (frameAt original.source [closingWord] 3).payments slot = some 2 := by
      decide +kernel
    exact found slot
  distinctDebits := two_actual_debits_cover_the_original_mandate
  closed := by decide +kernel
  next := OutstandingSource.History.actual_next original.source [closingWord] 1

def empty_suffix_leaves_the_original_mandate_service_unpaid :
    Issue original [] [] := by
  let first : original.source.Slot := ⟨0, by decide⟩
  exact .service first (((serviceThread original [] [] first).native_live_iff_unpaid original.source).mpr
    (by decide +kernel))

private theorem literal_clock (suffix : List (List Source.Action)) :
    (target original [] suffix).clock = (suffix.length : ℚ) + 2 := by
  have clock := constant_source_duration_gives_the_literal_clock original suffix 1 (by decide) (fun _ => rfl)
    (suffix.length + 2)
  change clockAt original suffix (suffix.length + 2) = _
  rw [clock]
  change (0 : ℚ) + ((suffix.length + 2 : Nat) : ℚ) * 1 = _
  push_cast
  ring

theorem the_original_mandate_attains_the_earliest_joint_paid_clock :
    IsLeast (times original []) (3 : EReal) := by
  constructor
  · refine ⟨[closingWord], original_service_and_release_are_actually_paid, ?_⟩
    change (((target original [] [closingWord]).clock : ℝ) : EReal) = _
    rw [literal_clock]
    change (((((1 : ℚ) + 2) : ℚ) : ℝ) : EReal) = ((3 : ℝ) : EReal)
    norm_num
  · rintro _ ⟨suffix, paid, rfl⟩
    have count : 1 ≤ suffix.length := by
      cases suffix with
      | nil => exact (empty_suffix_leaves_the_original_mandate_service_unpaid.refutes paid).elim
      | cons _ _ => simp
    change (3 : EReal) ≤ (((target original [] suffix).clock : ℝ) : EReal)
    rw [literal_clock]
    apply EReal.coe_le_coe_iff.mpr
    have enough : (3 : ℚ) ≤ (suffix.length : ℚ) + 2 := by
      exact_mod_cast (show 3 ≤ suffix.length + 2 by omega)
    exact_mod_cast enough

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Consumers
