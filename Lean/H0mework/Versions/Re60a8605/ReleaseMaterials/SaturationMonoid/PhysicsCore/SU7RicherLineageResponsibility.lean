import H0mework.Physics.Admission.SU7SourcePhaseFieldAnchorCore
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7GeneratedResidualStandingBoundary

/-!
# Rich source/phase/field responsibility transport

This module lifts the generated endpoint-repair relation to a richer lineage
whose anchor remembers an endpoint-stable SU7/A6 source derivation, a
componentwise phase/H1 ledger, the affine rate `sigma`, and the generated
color-loop field.  A lifted repair step changes only the endpoint component.
The transitive closure therefore cannot silently replace or erase the richer
anchor.

The result is a transporter and responsibility-preservation theorem.  It does
not claim that the current physical source grammar independently produces the
phase/H1 cochain, and it does not import a thin/P950 terminal, endpoint
atomhood, `Nat.Prime`, or an arithmetic projection pair.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7RicherLineageResponsibility

open Relation
open StandardModelConstraint
open SU7GeneratedCenterCoverPath
open SU7GeneratedResidualStandingBoundary

noncomputable section


/-- Native lift of one generated endpoint repair.  The endpoint step remains
computed by the existing source closure; the rich anchor is exactly fixed. -/
structure RichGeneratedEndpointRepairStep
    (n bound : Nat)
    (source target : RichSourcePhaseFieldLineage) : Prop where
  anchor_eq : source.anchor = target.anchor
  originEndpoint_eq : source.originEndpoint = target.originEndpoint
  endpoint_step :
    GeneratedEndpointRepairStep n bound source.endpoint target.endpoint

abbrev RichRewriteStar (n bound : Nat) :=
  RewriteStar (RichGeneratedEndpointRepairStep n bound)

/-- Every existing endpoint rewrite path lifts to the richer carrier without
changing its source/phase/field anchor. -/
theorem liftEndpointRewriteStar
    {n bound : Nat} (source : RichSourcePhaseFieldLineage)
    {targetEndpoint : Nat × Nat}
    (H :
      RewriteStar (GeneratedEndpointRepairStep n bound)
        source.endpoint targetEndpoint) :
    RichRewriteStar n bound source (source.withEndpoint targetEndpoint) := by
  induction H with
  | refl =>
      simpa using
        (ReflTransGen.refl :
          RichRewriteStar n bound source source)
  | tail pathPrefix step ih =>
      exact ReflTransGen.tail ih
        { anchor_eq := rfl
          originEndpoint_eq := rfl
          endpoint_step := step }

/-- Projection of a rich legal path recovers the original generated endpoint
path; the residual responsibility trace is therefore not weakened. -/
theorem endpointRewriteStar_of_richRewriteStar
    {n bound : Nat} {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    RewriteStar (GeneratedEndpointRepairStep n bound)
      source.endpoint target.endpoint := by
  induction H with
  | refl => exact ReflTransGen.refl
  | tail _ step ih =>
      exact ReflTransGen.tail ih step.endpoint_step

/-- Legal rich repair paths preserve the entire non-endpoint anchor. -/
theorem anchor_eq_of_richRewriteStar
    {n bound : Nat} {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    source.anchor = target.anchor := by
  induction H with
  | refl => rfl
  | tail _ step ih => exact ih.trans step.anchor_eq

theorem originEndpoint_eq_of_richRewriteStar
    {n bound : Nat} {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    source.originEndpoint = target.originEndpoint := by
  induction H with
  | refl => rfl
  | tail _ step ih => exact ih.trans step.originEndpoint_eq

theorem sourcePathData_eq_of_richRewriteStar
    {n bound : Nat} {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    source.anchor.sourcePathData = target.anchor.sourcePathData :=
  congrArg SourcePhaseFieldAnchor.sourcePathData
    (anchor_eq_of_richRewriteStar H)

theorem phaseCochain_eq_of_richRewriteStar
    {n bound : Nat} {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    source.anchor.phaseCochain = target.anchor.phaseCochain :=
  congrArg SourcePhaseFieldAnchor.phaseCochain
    (anchor_eq_of_richRewriteStar H)

theorem h1Ledger_eq_of_richRewriteStar
    {n bound : Nat} {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    source.anchor.h1Ledger = target.anchor.h1Ledger :=
  congrArg SourcePhaseFieldAnchor.h1Ledger
    (anchor_eq_of_richRewriteStar H)

theorem sigma_eq_of_richRewriteStar
    {n bound : Nat} {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    source.anchor.sigma = target.anchor.sigma :=
  congrArg SourcePhaseFieldAnchor.sigma
    (anchor_eq_of_richRewriteStar H)

theorem field_eq_of_richRewriteStar
    {n bound : Nat} {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    source.anchor.field = target.anchor.field :=
  congrArg SourcePhaseFieldAnchor.field
    (anchor_eq_of_richRewriteStar H)

/-! ## Rich terminal responsibility certificate -/

/-- A rich trace contains a legal lifted path and the existing exact endpoint
step-count, energy, and signed-displacement responsibility ledger. -/
structure RichEndpointRepairResponsibilityTrace
    (n bound : Nat) (reference : Nat × Nat)
    (source target : RichSourcePhaseFieldLineage) : Prop where
  richPath : RichRewriteStar n bound source target
  endpointTrace :
    EndpointRepairResponsibilityTrace
      n bound reference source.endpoint target.endpoint

theorem richEndpointRepairResponsibilityTrace_of_richRewriteStar
    {n bound : Nat} (reference : Nat × Nat)
    {source target : RichSourcePhaseFieldLineage}
    (H : RichRewriteStar n bound source target) :
    RichEndpointRepairResponsibilityTrace
      n bound reference source target where
  richPath := H
  endpointTrace :=
    endpointRepairResponsibilityTrace_of_rewriteStar reference
      (endpointRewriteStar_of_richRewriteStar H)

/-- A legal terminal resolution is a rich generated repair path whose endpoint
has reached the zero-residual class. -/
structure LegalRichTerminalResolution
    (n bound : Nat)
    (source target : RichSourcePhaseFieldLineage) : Prop where
  richPath : RichRewriteStar n bound source target
  terminal_zero : endpointEnergy n target.endpoint = 0

/-- Terminal resolution cannot silently discard source-path, phase/H1, sigma,
field, or signed endpoint-residual responsibility. -/
theorem legalRichTerminalResolution_preserves_responsibility
    {n bound : Nat} (reference : Nat × Nat)
    {source target : RichSourcePhaseFieldLineage}
    (H : LegalRichTerminalResolution n bound source target) :
    source.originEndpoint = target.originEndpoint ∧
      source.anchor.sourceRoot = target.anchor.sourceRoot ∧
        source.anchor.sourcePathData = target.anchor.sourcePathData ∧
          source.anchor.phaseCochain = target.anchor.phaseCochain ∧
            source.anchor.h1Ledger = target.anchor.h1Ledger ∧
              source.anchor.sigma = target.anchor.sigma ∧
                source.anchor.field = target.anchor.field ∧
                  EndpointRepairResponsibilityTrace
                    n bound reference source.endpoint target.endpoint := by
  have hanchor := anchor_eq_of_richRewriteStar H.richPath
  exact
    ⟨originEndpoint_eq_of_richRewriteStar H.richPath,
      congrArg SourcePhaseFieldAnchor.sourceRoot hanchor,
      sourcePathData_eq_of_richRewriteStar H.richPath,
      phaseCochain_eq_of_richRewriteStar H.richPath,
      h1Ledger_eq_of_richRewriteStar H.richPath,
      sigma_eq_of_richRewriteStar H.richPath,
      field_eq_of_richRewriteStar H.richPath,
      endpointRepairResponsibilityTrace_of_rewriteStar reference
        (endpointRewriteStar_of_richRewriteStar H.richPath)⟩

/-- Existing endpoint terminal paths lift to legal rich terminal resolutions
over the exact same anchor. -/
theorem legalRichTerminalResolution_of_endpointRewriteStar
    {n bound : Nat} (source : RichSourcePhaseFieldLineage)
    {targetEndpoint : Nat × Nat}
    (H :
      RewriteStar (GeneratedEndpointRepairStep n bound)
        source.endpoint targetEndpoint)
    (hzero : endpointEnergy n targetEndpoint = 0) :
    LegalRichTerminalResolution n bound source
      (source.withEndpoint targetEndpoint) where
  richPath := liftEndpointRewriteStar source H
  terminal_zero := hzero

end
end SU7RicherLineageResponsibility
end PhysicsCore
end SaturationMonoid
