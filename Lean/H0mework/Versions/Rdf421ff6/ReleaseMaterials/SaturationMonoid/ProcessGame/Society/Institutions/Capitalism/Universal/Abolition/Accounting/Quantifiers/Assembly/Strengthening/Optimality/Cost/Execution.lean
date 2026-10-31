import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.CanonicalLinear
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Canonical
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count reader)
  (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
    input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source))

theorem the_costed_programme_is_the_same_completed_actual_root_physical_current :
    Public.Scope.actualState input depth count 0 0 [] (Clearing.Deployment.completedPosition source resources).actual.snapshot =
      Programme.run input (before source) (programme source) := by
  calc
    Public.Scope.actualState input depth count 0 0 [] (Clearing.Deployment.completedPosition source resources).actual.snapshot =
        Physical.Public.stateAt input depth count 0 0 [] (Clearing.Deployment.completedPosition source resources).past :=
      Clearing.Position.raw_state_is_read_from_its_actual_past (Clearing.Deployment.completedPosition source resources)
    _ = Physical.Public.stateAt input depth count 0 0 [] (source.past ++ programme source) := by
      rw [Clearing.Deployment.the_whole_clearing_has_the_same_original_actual_past]
      rfl
    _ = Programme.run input (before source) (programme source) :=
      (Programme.the_comparison_programme_is_the_literal_original_source_suffix input (programme source) depth count 0 0 [] source.past).symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Canonical
