import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Reader

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

abbrev firstOriginal (nature : RequestAt) :=
  Macro.Runtime.batchFrame (review := none) input 0 0 datum 0 0 (reader nature) 0

def closedOriginal (nature : RequestAt) :=
  Macro.Bound.after (firstOriginal nature) (Macro.Bound.minor (firstOriginal nature))

def firstRaw (nature : RequestAt) := Macro.Runtime.ActivatedFrame.originalBoundary (closedOriginal nature)
  (Macro.Bound.exact_original_inventory_closes_its_own_bookkeeping (firstOriginal nature)).1

def firstOrigin (nature : RequestAt) := (closedOriginal nature).controlOrigin (firstRaw nature).germ

theorem the_first_raw_boundary_is_source_generated (nature : RequestAt) :
    boundary nature 0 = .original (closedOriginal nature) := by
  calc
    boundary nature 0 = Macro.Runtime.ActivatedFrame.after (current nature 0)
        (current nature 0).complete.steps :=
      (Macro.Runtime.actual_internal_fold_is_the_same_registered_history (review := none)
        input 0 0 datum 0 0 (reader nature) 0 _).symm
    _ = .original (closedOriginal nature) := by
      change Macro.Runtime.ActivatedFrame.after (.original (firstOriginal nature))
        (Macro.Bound.minor (firstOriginal nature)) = _
      exact Macro.Runtime.ActivatedFrame.original_internal_prefix_is_the_original_paid_inventory
        (firstOriginal nature) _ (Nat.le_refl _)

private theorem after_keeps_reader
    (frame : Macro.Runtime.Frame (review := none) input 0 count 0 0 0 count) (steps : Nat) :
    (Macro.Bound.after frame steps).package.reader = frame.package.reader := by
  induction steps with
  | zero => rfl
  | succ steps prior =>
      exact (Macro.Runtime.reference_next_keeps_the_same_raw_reader _).trans prior

theorem the_first_raw_cut_keeps_the_original_reader_and_physical_prefix (nature : RequestAt) :
    (closedOriginal nature).package.reader = reader nature ∧
      (firstRaw nature).germ.snapshot = (firstOriginal nature).snapshot ∧
      (firstRaw nature).germ.raw = selected nature (firstRaw nature).germ.snapshot.past := by
  have sameReader : (closedOriginal nature).package.reader = reader nature :=
    (after_keeps_reader (firstOriginal nature) _).trans rfl
  have original := Macro.Raw.input_uses_the_literal_current_account
    (closedOriginal nature).package.source (closedOriginal nature).package.sourceData
    (closedOriginal nature).package.reader (firstRaw nature).germ
  refine ⟨sameReader, original.2.1.trans
      (Macro.Bound.exact_original_inventory_closes_its_own_bookkeeping (firstOriginal nature)).2, ?_⟩
  exact original.2.2.trans
    (congrFun (congrFun sameReader (firstRaw nature).germ.snapshot) (firstRaw nature).germ.account)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
