import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer.Needs
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime.Complete

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation.Control

noncomputable section

local instance : Finite native.root.toAuthoritativeRoot.source.projectionLaw.Projection := original.projectionFinite

/-- The origin seal is generated here from the already existing controlled
source and its fully consumed native inventory; consumers supply only an actual input. -/
theorem every_actual_input_has_the_complete_original_source_accounting (word : Word) :
    Action.Runtime.SameSourceAccountingAt input native visit C.familyClaim originalOrigin word originalAuthority :=
  Action.Runtime.the_original_source_installs_and_consumes_its_complete_accounting
    input native visit C.familyClaim originalOrigin word originalAuthority

theorem the_original_controlled_capital_obligation_has_its_paid_same_root_successor :
    Action.Runtime.SameSourceAccountingAt input native visit C.familyClaim originalOrigin C.matrixWord originalAuthority ∧
      Responsibility.Family.State.isPaid C.familyClaim (actualState C.matrixWord) ∧
      match actualNeeds C.matrixWord with
      | .paid _ => True
      | .necessity .. | .maintenance .. => False :=
  ⟨every_actual_input_has_the_complete_original_source_accounting C.matrixWord,
    the_same_named_runtime_really_pays_all_original_material_and_result_cells,
    the_actual_root_need_report_accepts_the_paid_full_matrix⟩

#print axioms every_actual_input_has_the_complete_original_source_accounting
#print axioms the_original_controlled_capital_obligation_has_its_paid_same_root_successor

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer
