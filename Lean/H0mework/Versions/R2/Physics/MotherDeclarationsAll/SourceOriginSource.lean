import H0mework.Versions.R2.Physics.MotherDeclarationsAll.SourceOriginOperations

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open StageNineEnrichedProofFreeSource StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyWholeSpacetimeAssembly
open StageNineDiracDualFormNativeJointResidualCarrier

noncomputable section

def residual (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source) : RootResidualPayload :=
  { coframeBoundary := .settled
    classicalJoint := diracDualFormNativeJointResidualSection source state.current
    gravity := 0
    gravityCoframeFirstJet := 0
    assembly := candidateAssemblySeam source state.current }

structure OpenAt (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source)
    (responsibility : RootResidualPayload) : Type where
  exact : responsibility = residual source state

abbrev ObstructionAt (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source) :=
  Σ coordinate : RootResidualCoordinate, Σ point : BasePoint,
    (residual source state).coordinateAt coordinate point

abbrev Claim (source : SmoothUnifiedSource) := RootResidualClaim ⊕ Sigma (ObstructionAt source)

def holds (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source) : Claim source → Type
  | .inl .liveAccount => PUnit
  | .inl (.obstruction _) => PEmpty
  | .inr obstruction => PLift (obstruction.1 = state)

/-- The original full physical residual vocabulary is parameterized by its actual source. -/
def network (source : SmoothUnifiedSource) : WorldRelationNetwork where
  Support := GeneralSourceEvolution.State source
  Anchor := SmoothUnifiedSource
  Incidence := GeneralSourceEvolution.State source
  Lineage := SmoothUnifiedSource
  Responsibility := RootResidualPayload
  Claim := Claim source
  anchorAt := fun _ => source
  incidenceAt := id
  lineageAt := fun _ => source
  OpenAt := OpenAt source
  openClaimAt := fun _ => .inl .liveAccount
  HoldsAt := holds source
  ObstructionAt := ObstructionAt source
  obstructionClaim := fun {state} obstruction => .inr ⟨state, obstruction⟩
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun _ kind => match kind with
    | .transfer => BasePoint
    | .supportSettlement | .lawSurfaceExtension => PEmpty

def entry (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source) :
    OpenResponsibilityAt (network source) state := ⟨residual source state, ⟨rfl⟩⟩

theorem entry_unique (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source)
    (value : OpenResponsibilityAt (network source) state) : value = entry source state := by
  rcases value with ⟨responsibility, ⟨same⟩⟩
  cases same
  rfl

def inventory (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source) :
    ConstructivePresentation PUnit (OpenResponsibilityAt (network source) state) where
  forward := fun _ => entry source state
  backward := fun _ => PUnit.unit
  backward_forward := fun _ => rfl
  forward_backward := fun value => (entry_unique source state value).symm

structure EventAt (source : SmoothUnifiedSource) (current support : GeneralSourceEvolution.State source) : Type where
  center : BasePoint
  support_eq : support = current

def eventAlgebra (law : Law) (source : SmoothUnifiedSource) :
    SourceNativeEventAlgebra (network source) (vocabulary law source) where
  EventAt := EventAt source
  compile := fun event => .nativeWrite event.center
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.support_eq
    exact inventory source current
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.support_eq.symm
  lineage_commutes := fun _ => rfl

def sourceAt (law : Law) (material : Material) :
    SourceNativeSource (network (input material).1) (vocabulary law (input material).1) where
  initial := (input material).2.1
  law := eventAlgebra law (input material).1

def emitted (law : Law) (material : Material) (current : GeneralSourceEvolution.State (input material).1) :
    (sourceAt law material).toRootSource.actual.OccurrenceAt current :=
  ⟨current, ⟨(input material).2.2, rfl⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin
