import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWardGram.Bilinear
import Lean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
namespace Paid
-- Two exact signed144 dependent selectors; their elaboration emits only original constants.
open Lean Elab Command in
run_elab do
  let source := Lean.mkPrivateNameCore `H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Source `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard.value_of_actual_input
  let original ← Lean.getConstInfo source
  let namespaceName ← getCurrNamespace
  Lean.addAndCompile (.defnDecl {
    name := namespaceName ++ `value_of_actual_input
    levelParams := original.levelParams
    type := original.type
    value := Lean.mkConst source (original.levelParams.map Lean.Level.param)
    hints := .abbrev
    safety := .safe })
open Lean Elab Command in
run_elab do
  let source := Lean.mkPrivateNameCore `H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Effect `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard.material_raw_at
  let original ← Lean.getConstInfo source
  let namespaceName ← getCurrNamespace
  Lean.addAndCompile (.defnDecl {
    name := namespaceName ++ `material_raw_at
    levelParams := original.levelParams
    type := original.type
    value := Lean.mkConst source (original.levelParams.map Lean.Level.param)
    hints := .abbrev
    safety := .safe })
end Paid
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
