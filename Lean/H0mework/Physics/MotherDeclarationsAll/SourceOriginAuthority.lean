import H0mework.Physics.MotherDeclarationsAll.SourceOriginLedger
import H0mework.Physics.CartanReduction.P286Descent

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open Stage9C.Reduction

noncomputable section

variable (law : Law) (material : Material)

private def restructuringLaw : SourceNativeLedgerRestructuringLaw (sourceAt law material) :=
  identityOnlyWorldLedgerRestructuringLaw (sourceAt law material) (input material).1 <| by
    intro state responsibility
    constructor
    rintro ⟨first⟩ ⟨second⟩
    rfl

private def restructuringCompiler : SourceNativeRestructuringLedgerCompiler (sourceAt law material) where
  ledgerCompiler := compiler law material
  restructuringLaw := restructuringLaw law material
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (entry_unique _ _ left).trans (entry_unique _ _ right).symm)
    (fun left right _ => (entry_unique _ _ left).trans (entry_unique _ _ right).symm)

def restructuringSource : SourceNativeRestructuringLedgerSource
    (network (input material).1) (vocabulary law (input material).1) where
  source := sourceAt law material
  compiler := restructuringCompiler law material

/-- Full input, full next input, both physical residuals, whole ledger and original action are source fields. -/
def projectionLaw : SourceNativeProjectionLaw (ledgerSource law material) where
  Projection := Fin 6
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ =>
    match projection with
    | 0 | 1 => JointSourceLaws.Input
    | 2 | 3 => RootResidualPayload
    | 4 => SourceNativeLedgerEvolutionAt (sourceAt law material) occurrence
    | 5 => ℝ
  project := fun projection {current} occurrence _ =>
    match projection with
    | 0 => ⟨(input material).1, current, occurrence.2.center⟩
    | 1 => ⟨(input material).1, target law material occurrence, occurrence.2.center⟩
    | 2 => residual (input material).1 current
    | 3 => residual (input material).1 (target law material occurrence)
    | 4 => (compiler law material).compile occurrence
    | 5 => actualRelativeAction (input material).1 current.current (target law material occurrence).current

def authoritySource : SourceNativeAuthoritySource (network (input material).1) (vocabulary law (input material).1) where
  restructuringSource := restructuringSource law material
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource law material)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic (network (input material).1)
  projectionLaw := projectionLaw law material

def authoritativeRoot : SourceNativeAuthoritativeRootClosure
    (network (input material).1) (vocabulary law (input material).1) where
  source := authoritySource law material
  emitted := emitted law material
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure
    (network (input material).1) (vocabulary law (input material).1) :=
  (authoritativeRoot law material).toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin
