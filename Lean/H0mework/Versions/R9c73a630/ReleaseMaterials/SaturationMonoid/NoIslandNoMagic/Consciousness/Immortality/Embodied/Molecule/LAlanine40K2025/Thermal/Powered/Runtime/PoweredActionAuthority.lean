import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Runtime.PoweredActionLedger
import H0mework.Versions.R9c73a630.Chemistry.LAlanineThermalRuntime.GeneratedPoweredCapacity

/-! # The controlled law installs its material and quantitative consumers before emission -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Producer

noncomputable section

private def poweredRestructuringLaw : SourceNativeLedgerRestructuringLaw poweredSource :=
  identityOnlyWorldLedgerRestructuringLaw poweredSource LAlanine40K2025.Source.key (by
    intro support responsibility
    cases support with
    | inl oldSupport =>
      cases oldSupport with
      | inl stage => exact Root.networkOpenAtSubsingleton stage responsibility
      | inr _ => exact inferInstanceAs (Subsingleton PUnit)
    | inr _ =>
      change Subsingleton PUnit
      infer_instance)

private def poweredRestructuringCompiler : SourceNativeRestructuringLedgerCompiler poweredSource where
  ledgerCompiler := poweredLedgerCompiler
  restructuringLaw := poweredRestructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (poweredEntry_unique _ left).trans (poweredEntry_unique _ right).symm)
    (fun left right _ => (poweredEntry_unique _ left).trans (poweredEntry_unique _ right).symm)

def poweredRestructuringSource : SourceNativeRestructuringLedgerSource PoweredN PoweredV where
  source := poweredSource
  compiler := poweredRestructuringCompiler

inductive PoweredProjection
  | initial
  | current
  | next
  | pairEnergy
  | controllerEnergy
  | energyBalance
  | energyBound
  | capacities
  | capacityBalance
  | wholeLedger

def poweredCapacitiesRead (current : PoweredState) : ℝ × ℝ × ℝ :=
  (poweredPairCapacity current, poweredControllerCapacity current, poweredJointCapacity current)

def poweredProjectionLaw : SourceNativeProjectionLaw poweredRestructuringSource.toLedgerSource where
  Projection := PoweredProjection
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .initial | .current | .next => PoweredState
    | .pairEnergy | .controllerEnergy => ℝ
    | .energyBalance => PLift (type_of% (poweredStateNext_energyBalance (poweredCurrentState current)))
    | .energyBound => PLift (type_of% (poweredStateNext_energyBound (poweredCurrentState current)))
    | .capacities => (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)
    | .capacityBalance => PLift (type_of% (poweredLocal_capacityBalance (poweredCurrentState current)) ∧
        type_of% (poweredJoint_capacityConserved (poweredCurrentState current)))
    | .wholeLedger => SourceNativeLedgerEvolutionAt poweredSource occurrence
  project := fun projection {current} occurrence _ =>
    match projection with
    | .initial => sourceInitialState
    | .current => poweredCurrentState current
    | .next => poweredStateNext (poweredCurrentState current)
    | .pairEnergy => poweredPairEnergy (poweredCurrentState current)
    | .controllerEnergy => poweredControllerEnergy (poweredCurrentState current)
    | .energyBalance => ⟨poweredStateNext_energyBalance (poweredCurrentState current)⟩
    | .energyBound => ⟨poweredStateNext_energyBound (poweredCurrentState current)⟩
    | .capacities => (poweredCapacitiesRead (poweredCurrentState current),
        poweredCapacitiesRead (poweredStateNext (poweredCurrentState current)))
    | .capacityBalance => ⟨poweredLocal_capacityBalance (poweredCurrentState current),
        poweredJoint_capacityConserved (poweredCurrentState current)⟩
    | .wholeLedger => poweredLedgerCompiler.compile occurrence

def poweredAuthoritySource : SourceNativeAuthoritySource PoweredN PoweredV where
  restructuringSource := poweredRestructuringSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal poweredRestructuringSource
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic PoweredN
  projectionLaw := poweredProjectionLaw

def poweredAuthoritativeRoot : SourceNativeAuthoritativeRootClosure PoweredN PoweredV where
  source := poweredAuthoritySource
  emitted := poweredEmitted
  compiler_commutes := fun _ => rfl

def poweredLivingRoot : SourceNativeLivingRootClosure PoweredN PoweredV :=
  poweredAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def poweredInitialVisit : SourceNativeTemporalVisitAt poweredLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite poweredLivingRoot.toAuthoritativeRoot.toRoot.initialVisit

def poweredInitialGenerated :=
  poweredLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit poweredInitialVisit

def poweredInitialEntry := poweredEntry (poweredCurrentSupport .ingress)

def poweredInitialEntryRow : poweredInitialGenerated.GeneratedEntryRowAt poweredInitialEntry :=
  (poweredInitialGenerated.canonicalGeneratedEntryRow? poweredInitialEntry).get (by rfl)

def poweredFirstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    poweredInitialGenerated.occurrence poweredInitialGenerated.wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? poweredInitialGenerated.wholeLedgerWriteBack).get (by rfl)

end

end LAlanine40K2025.Thermal.Powered.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
