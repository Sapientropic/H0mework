import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Release

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing

private theorem filterMap_erase_none {S A : Type} [DecidableEq S]
    (read : S → Option A) (stock : List S) (item : S) (ignored : read item = none) :
    (stock.erase item).filterMap read = stock.filterMap read := by
  induction stock with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : first = item
    · subst first
      simp [ignored]
    · cases value : read first <;> simp [same,value,ih]

private theorem consume_filterMap {S A : Type} [DecidableEq S]
    (read : S → Option A) (required stock remainder : List S)
    (ignored : ∀ item ∈ required, read item = none)
    (actual : Inventory.consume required stock = .ok remainder) :
    remainder.filterMap read = stock.filterMap read := by
  induction required generalizing stock with
  | nil => cases Except.ok.inj actual; rfl
  | cons first rest ih =>
    change (if first ∈ stock then Inventory.consume rest (stock.erase first)
      else .error first) = .ok remainder at actual
    split at actual
    · have after := ih (stock.erase first) (fun item member => ignored item (by simp [member])) actual
      exact after.trans (filterMap_erase_none read stock first (ignored first (by simp)))
    · cases actual

theorem inventory_filterMap_preserved {S A R : Type} [DecidableEq S]
    (read : S → Option A) (reactants products : R → List S) (program : List R) (stock : List S)
    (ignored : ∀ reaction ∈ program,
      (∀ item ∈ reactants reaction, read item = none) ∧ (products reaction).filterMap read = []) :
    (Inventory.execute reactants products program stock).stock.filterMap read = stock.filterMap read := by
  induction program generalizing stock with
  | nil => rfl
  | cons reaction rest ih =>
    cases consumed : Inventory.consume (reactants reaction) stock with
    | error missing =>
      rw [Inventory.execute_cons]
      simp only [Inventory.fire,consumed]
    | ok remainder =>
      have old := consume_filterMap read _ _ _ (ignored reaction (by simp)).1 consumed
      have later := ih (products reaction ++ remainder) (fun next member => ignored next (by simp [member]))
      have same : (products reaction ++ remainder).filterMap read = stock.filterMap read := by
        rw [List.filterMap_append,(ignored reaction (by simp)).2,List.nil_append]
        exact old
      change (Inventory.execute reactants products (reaction :: rest) stock).stock.filterMap read = _
      rw [Inventory.execute_cons]
      simpa only [Inventory.fire,consumed] using later.trans same

def nativeDNA? : Species → Option (List CPS1Deamination.Base)
  | .dna word => some word
  | _ => none

def notDeamination (reaction : Reaction) : Prop :=
  match reaction with | .deaminate _ _ => False | _ => True

private theorem no_native_dna_change (reaction : Reaction) (safe : notDeamination reaction) :
    (∀ item ∈ reaction.reactants, nativeDNA? item = none) ∧ reaction.products.filterMap nativeDNA? = [] := by
  cases reaction <;> simp [notDeamination] at safe
  all_goals simp [Reaction.reactants,Reaction.products,nativeDNA?,factorStock]

private theorem elongation_not_deamination (chain : Peptide) (tail : List AA) :
    ∀ reaction ∈ Program.compileElongation chain tail, notDeamination reaction := by
  induction tail generalizing chain with
  | nil => simp [Program.compileElongation]
  | cons aa rest ih =>
    intro reaction member
    simp only [Program.compileElongation,List.mem_cons] at member
    rcases member with rfl | rfl | rfl | later
    · trivial
    · trivial
    · trivial
    · exact ih (chain.extend aa) reaction later

private theorem compile_not_deamination (tail : List AA) :
    ∀ reaction ∈ CPS1InitiationTermination.UnifiedBoundary.compile tail, notDeamination reaction := by
  intro reaction member
  simp only [CPS1InitiationTermination.UnifiedBoundary.compile,List.mem_append,List.mem_cons,List.mem_map] at member
  rcases member with initial | terminated
  · rcases initial with initialSteps | extended
    · rcases initialSteps with charging | loading
      · rcases charging with rfl | charged
        · trivial
        · rcases charged with ⟨aa,_,rfl⟩; trivial
      · rcases loading with rfl | rfl | impossible
        · trivial
        · trivial
        · cases impossible
    · cases tail with
      | nil => cases extended
      | cons aa rest =>
        simp only [CPS1InitiationTermination.UnifiedBoundary.elongation,List.mem_append,List.mem_cons] at extended
        rcases extended with (rfl | rfl | rfl | impossible) | later
        · trivial
        · trivial
        · trivial
        · cases impossible
        · exact elongation_not_deamination (.M,[aa]) rest reaction later
  · cases tail <;>
      simp [CPS1InitiationTermination.UnifiedBoundary.termination] at terminated <;>
      rcases terminated with rfl | rfl <;> trivial

theorem native_translation_preserves_genome (tail : List AA) (stock : Stock) :
    CPS1Deamination.ExecutionReadout.readDNA (execute (CPS1InitiationTermination.UnifiedBoundary.compile tail) stock).stock =
      CPS1Deamination.ExecutionReadout.readDNA stock := by
  have same := inventory_filterMap_preserved nativeDNA? Reaction.reactants Reaction.products
    (CPS1InitiationTermination.UnifiedBoundary.compile tail) stock
    (fun reaction member => no_native_dna_change reaction (compile_not_deamination tail reaction member))
  exact congrArg List.head? same

end
end CPS1BiologicalUpdate
