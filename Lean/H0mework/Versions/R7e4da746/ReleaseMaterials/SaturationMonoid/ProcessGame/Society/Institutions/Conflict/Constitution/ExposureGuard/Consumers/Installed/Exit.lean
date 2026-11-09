import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed.Period
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Root
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Exercise

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed

open Capitalism.Universal.Source.Program Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Quantities.Execution (endAt inventory)

noncomputable section

def noControl : Raw → List Bool := fun _ => []

private theorem no_foreign_debit (damage : Boundary.Actual.DamageAt cut service id) : False := by
  have listed := damage.source_item
  rw [inventory_exact] at listed
  have check : ∀ item ∈ material.rawItems cutRaw lifeWord, ∀ victim attacker good : Bool,
      ¬ 0 < Reparation.loss material id item (victim, attacker, good) := by decide +kernel
  have positive := damage.positive
  change 0 < Reparation.loss (Physical.Public.interpreter cut.native.input) id damage.item damage.key at positive
  rw [cut_input] at positive
  exact check damage.item listed damage.key.1 damage.key.2.1 damage.key.2.2 positive

private theorem original_signature (request : Req) (listed : request ∈ signedRequests service) :
    OwnSignature cut [] request :=
  ⟨standing _, List.not_mem_nil, (by decide +kernel : ∀ req ∈ lifeWord, req.consents = []) request listed⟩

private theorem original_material (item : Item) (listed : item ∈ Boundary.Actual.items cut service) :
    OwnMaterial cut [] item := by
  rw [inventory_exact] at listed
  refine ⟨⟨standing _, List.not_mem_nil, ?_, ?_⟩, ?_⟩
  · exact (by decide +kernel : ∀ req ∈ material.rawItems cutRaw lifeWord, req.request.consents = []) item listed
  · change ∀ entry ∈ (Physical.Public.interpreter cut.native.input).actualDebit item.before item.request,
      0 < entry.2 → entry.1.1 = item.request.signer
    rw [cut_input]
    exact (by decide +kernel : ∀ original ∈ material.rawItems cutRaw lifeWord,
      ∀ entry ∈ material.actualDebit original.before original.request,
        0 < entry.2 → entry.1.1 = original.request.signer) item listed
  · rw [cut_input]
    exact (by decide +kernel : ∀ original ∈ material.rawItems cutRaw lifeWord,
      active.Valid original.before original.request) item listed

private theorem self_exposure (item : Item) (actual : item ∈ Boundary.Actual.items cut service) :
    Exit.OwnExposure cut noControl item := by
  refine ⟨List.not_mem_nil, ?_⟩
  have listed := actual
  rw [inventory_exact] at listed
  intro question asked
  simp only [questions, List.mem_cons, List.mem_append] at asked
  rcases asked with signature | debit | finance
  · exact congrArg Prod.fst signature
  · obtain ⟨entry, original, same⟩ := List.mem_filterMap.mp debit
    change entry ∈ (Physical.Public.interpreter cut.native.input).actualDebit item.before item.request at original
    rw [cut_input] at original
    have self : entry.1.1 = item.request.signer :=
      (by decide +kernel : ∀ row ∈ material.rawItems cutRaw lifeWord,
        ∀ line ∈ material.actualDebit row.before row.request, line.1.1 = row.request.signer)
        item listed entry original
    dsimp only at same
    split at same
    · exact (congrArg Prod.fst (Option.some.inj same)).symm.trans self
    · cases same
  · have none : financialQuestions item = [] :=
      (by decide +kernel : ∀ row ∈ material.rawItems cutRaw lifeWord, financialQuestions row = []) item listed
    rw [none] at finance
    exact (List.not_mem_nil finance).elim

theorem pays_each_original_member (person : Bool) :
    window.timely [] service (person, .necessity, true, 1) = 1 := by
  have eligible (item : Item) (listed : item ∈ Boundary.Actual.items cut service) :
      decide (OwnMaterial cut [] item) = true := decide_eq_true (original_material item listed)
  unfold Window.timely
  change (if (window.nextCut service).raw.clock ≤ window.deadline then
    (((Boundary.Actual.items cut service).filter fun item => decide (OwnMaterial cut [] item)).map
      fun item => flowAt (Optimality.Cost.actualPart cut.native.handlerFace.rootRead
        item.before item.request (.use .necessity)) person true).sum else 0) + 0 = 1
  rw [if_pos deadline_exact.le, add_zero, List.filter_eq_self.mpr eligible, inventory_exact]
  change ((material.rawItems cutRaw lifeWord).map fun item =>
    flowAt (Optimality.Cost.actualPart (Physical.Public.interpreter cut.native.input)
      item.before item.request (.use .necessity)) person true).sum = 1
  rw [cut_input]
  cases person <;> decide +kernel

private theorem due_paid (cell : Cell) (listed : cell ∈ window.cells cut []) :
    cell.2.2.2 ≤ window.timely [] service cell := by
  let cells := Boundary.floorCells cut (window.residents cut [])
  have same := List.mem_dedup.mp listed
  change cell ∈ cells ++ cells ++ cells at same
  simp only [List.mem_append, or_self] at same
  obtain ⟨person, rfl⟩ := requirements_are_native cell (List.mem_filter.mp same).1
  exact (pays_each_original_member person).ge

theorem paid_round : RoundGood cut [] id window exitWord [] := by
  refine ⟨?_, ⟨⟨no_foreign_debit, fun person _ => successor_standing person,
    fun _ => original_signature, fun _ => original_material, fun _ => deadline_exact.le,
    fun _ => due_paid⟩, trivial⟩, ?_, trivial⟩
  · intro empty
    have original : false ∈ Civil.protectedMembers cut [] :=
      List.mem_filter.mpr ⟨standing false, rfl⟩
    have resident := Window.includes_current_resident cut [] window original
    exact List.not_mem_nil (empty ▸ resident)
  · rw [Window.run_current]
    change cut.raw.clock < (endAt cut exitWord).raw.clock
    rw [← clock_advances]
    exact lt_add_of_pos_right _ zero_lt_one

private theorem independent_exit : Exit.Certificate cut id [] [] noControl exitWord := by
  refine ⟨⟨fun person _ => standing person, fun person _ => successor_standing person⟩,
    self_exposure, ?_, paid_round⟩
  intro cell listed
  let people := Exit.roster cut (id : Bool → Bool) [] []
  have original : cell ∈ Exit.needsAt cut people ++ Exit.needsAt cut people := List.mem_dedup.mp listed
  have present : cell ∈ Exit.needsAt cut people := (List.mem_append.mp original).elim id id
  unfold Exit.needsAt at present
  rw [cut_input] at present
  obtain ⟨person, rfl⟩ := native_cell _ _ cell present
  change (1 : ℚ) ≤ window.timely [] service (person, .necessity, true, 1)
  exact (pays_each_original_member person).ge

theorem certificate : MandateExit.Certificate base scope cut id [] [] noControl exitWord := by
  refine ⟨independent_exit, ?_⟩
  intro item listed
  change item ∈ Boundary.Actual.items cut service at listed
  rw [inventory_exact] at listed
  exact (by decide +kernel : ∀ entry ∈ material.rawItems cutRaw lifeWord,
    MandateExit.TitleFree base scope entry) item listed

theorem available : MandateExit.Available base scope cut id [] [] noControl := ⟨exitWord, certificate⟩

theorem live_certificate : MandateExit.LiveCertificate cut [] [] id base scope noControl exitWord := by
  refine ⟨certificate, ?_⟩
  change Due.Checked cut window exitWord
  exact Due.of_original_civilian_check cut window id true exitWord paid_round.own

theorem live_available : MandateExit.LiveAvailable cut [] [] id base scope noControl :=
  ⟨exitWord, live_certificate⟩

def opened : GuardedVisit base scope cut (id : Bool → Bool) [] noControl :=
  ExposureGuard.start base scope cut id [] noControl live_available

theorem the_finite_installed_exit_check_opens_the_original_root :
    ExposureGuard.install base scope cut id [] noControl exitWord = .inr opened := by
  unfold ExposureGuard.install
  cases MandateExit.inspectLive cut [] [] (id : Bool → Bool) base scope noControl exitWord with
  | inl failed => exact (failed.refutes _ _ _ _ _ _ _ live_certificate).elim
  | inr accepted => rfl

def yes : OwnerAnswers cut := fun _ _ _ _ => true

def chosen : MandateExit.Chosen opened yes :=
  ⟨exitWord, live_certificate, ⟨fun _ => rfl, trivial⟩⟩

theorem the_installed_root_pays_both_original_exits_on_its_actual_clock :
    Quantities.Recorded cut exitWord ∧
      (cut.raw.clock + 1 = (endAt cut exitWord).raw.clock) ∧
      (∀ person, window.timely [] service (person, .necessity, true, 1) = 1) ∧
      (MandateExit.exercise opened chosen).stack.balances.map Prod.fst =
        Reparation.Actual.originalLosses cut id exitWord := by
  have paid := MandateExit.an_owner_selected_exit_pays_on_the_same_original_ledger opened chosen
  exact ⟨paid.1, clock_advances, pays_each_original_member, paid.2.2.2.2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed
