import H0mework.Physics.Cartan.CartanTorsionCoordinate
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.Coframe.CoframeSectorBalance
import H0mework.Physics.DualVariation.JointResidualCarrier
import H0mework.Physics.Geometry.JointShellStationarity
import H0mework.Physics.GaugeStanding.IntegratedWard

/-!
# S9-C single-current classical-world acceptance boundary

This module defines the target-shaped S9-C consumer without presenting it as
a source producer.  The current key is indexed by one already fixed root
current.  It consumes the authoritative Dirac-dual residual zero fibre, the
dynamic scalar's source contact, and the six nonzero physical departments on
that same current.

The former frozen-family/raw-action consumer remains below under explicit
`Legacy*` names.  Its whole-field static-vacuum clause and old absolute-action
hash are not part of the current key.

Neither key is a writer, root, lock, branch selector, or source producer.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance

open ProofFreeRicherAnholonomicSource
open StageNineCartanActionCoframeSecondJetLocalActualLift
open StageNineCoframeLocalDifferentiability
open StageNineCoframeSectorBalance
open StageNineCoframeSectorStress
open StageNineConnectionSectorSourceBalance
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineJointShellStationarity
open StageNineJointShellResidualCarrier
open StageNineJointShellZeroFiber
open StageNineLorentzConnectionVariation
open StageNineP286FrozenSourceScalarTorque
open StageNineP286Bianchi
open StageNineP286GaugeConnectionVariation
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveIntegratedWard
open StageNineP286LinkedActiveVariation
open SU7ExteriorBreakingYukawa
open MeasureTheory

noncomputable section

set_option autoImplicit false

universe u

/-- The source-relative active Ward law that is true for the frozen-source
action grammar.  Its derivative is the transported torque responsibility,
not a hand-filled zero. -/
def LegacyIntegratedSourceRelativeP286Ward
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ gaugeParameter : P286InfinitesimalGaugeParameter,
    HasDerivAt
      (fun parameter =>
        holonomicIntegratedUnifiedAction source 0
          (p286LinkedActivePrimitivePath configuration gaugeParameter
            parameter))
      (∫ point : BasePoint,
        p286FrozenSourceScalarTorqueDensity source configuration
          gaugeParameter point)
      0

/-- The integrated Ward law is a derived action readout from the actual
domain hypotheses. -/
theorem smooth_nondegenerate_integrable_implies_legacyIntegratedSourceRelativeP286Ward
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration) :
    LegacyIntegratedSourceRelativeP286Ward source configuration := by
  intro gaugeParameter
  exact
    holonomicIntegratedUnifiedAction_p286LinkedActivePrimitivePath_hasDerivAt_torque
      source configuration smooth nondegenerate densityIntegrable
        gaugeParameter

/-- Nonzero P286 matter current at one actual spacetime point. -/
def MatterCurrentNonzeroAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  ∃ direction : P286GaugeOneForm,
    p286MatterCurrentCoefficient source configuration direction point ≠ 0

/-- Nonzero Lorentz spin source at one actual spacetime point. -/
def MatterSpinNonzeroAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  ∃ direction : LorentzBivectorOneForm,
    lorentzMatterSpinSourceCoefficient source configuration direction point ≠ 0

/-- The sixth witness accepts either the exterior-matter sector stress or the
Lorentz matter-spin source.  The total coframe Euler covector is deliberately
excluded: full stationarity forces that total covector to vanish while the
action-owned sectors can remain nonzero and balance one another. -/
def StressOrSpinNonzeroAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  coframeMatterSectorStressCovector source point
      (toContinuumPointField configuration point) ≠ 0 ∨
    MatterSpinNonzeroAt source configuration point

/-- Historical six-sector shape tied to one source and one configuration.  Spacetime
witness points may differ: "same world" means the same on-shell family member,
not an extra coincidence at one coordinate.  The scalar equality prevents
source-level vacuum and mass readouts from being attached to an unrelated
actual scalar field. -/
structure LegacySimultaneousSixSectorNonzero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop where
  scalarGeneratedVacuum :
    configuration.scalar = generatedLocalVacuumCoordinates source 0
  gravityCurvature :
    ∃ point, holonomicGravityCurvature configuration point ≠ 0
  p286GaugeCurvature :
    ∃ point, holonomicGaugeCurvature configuration point ≠ 0
  breakingVacuum :
    sourceGeneratedVacuumBase source ≠ 0
  yukawaMass :
    exteriorYukawaMassMap (sourceGeneratedVacuumBase source) ≠ 0
  matterCurrent :
    ∃ point, MatterCurrentNonzeroAt source configuration point
  stressOrSpin :
    ∃ point, StressOrSpinNonzeroAt source configuration point

/-- Einstein--Cartan nondegeneracy at the acceptance boundary: a nonzero
same-actual spin source must leave at least one nonzero Cartan torsion
coordinate at the same point. -/
def SpinTorsionCompatible
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point,
    MatterSpinNonzeroAt source configuration point →
      ∃ first second internal : LorentzianIndex,
        cartanTorsionCoordinate configuration point first second internal ≠ 0

/-- Historical indexed classical-world family.  The index is deliberately generic and
does not by itself represent physical time, continuity, a flow, or branch
selection.  A downstream `source-generated` theorem must define its canonical
index and family directly from the proof-free source/action. -/
abbrev LegacyStageNineCClassicalWorldFamily (ι : Type u) :=
  ι → StageNineHolonomicConfiguration

/-- Legacy frozen-source S9-C consumer.  It deliberately stores neither strong equations,
zero-fiber membership, Bianchi identities, sector balances, nor the integrated
Ward law, because those are derived from the fields below. -/
structure LegacyClassicalWorldAcceptance
    (source : SmoothUnifiedSource)
    {ι : Type u}
    (family : LegacyStageNineCClassicalWorldFamily ι) : Prop where
  smooth :
    ∀ epoch, (family epoch).Smooth
  nondegenerate :
    ∀ epoch, (family epoch).Nondegenerate
  gravityConnectionLorentzAdmissible :
    ∀ epoch, GravityConnectionLorentzAdmissible (family epoch)
  densityIntegrable :
    ∀ epoch, HolonomicLocalDensityIntegrable source 0 (family epoch)
  fullActionStationary :
    ∀ epoch, CurrentFullActionStationary source (family epoch)
  simultaneousSixSectorNonzero :
    ∃ epoch, LegacySimultaneousSixSectorNonzero source (family epoch)
  spinTorsionCompatible :
    ∀ epoch, SpinTorsionCompatible source (family epoch)

/-- Full strong equations are derived from the nine primitive stationarity
channels on the same family member. -/
theorem LegacyClassicalWorldAcceptance.strongEquation
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι) :
    CurrentStrongJointShellEquation source (family epoch) :=
  currentFullActionStationary_implies_strongEquation source (family epoch)
    (acceptance.smooth epoch)
    (acceptance.nondegenerate epoch)
    (acceptance.densityIntegrable epoch)
    (acceptance.fullActionStationary epoch)

/-- Joint-shell zero is a transporter/readout of stationarity, not an
independent acceptance field. -/
theorem LegacyClassicalWorldAcceptance.jointShellZeroFiber
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι) :
    CurrentJointShellZeroFiber source (family epoch) :=
  currentFullActionStationary_implies_jointShellZeroFiber source
    (family epoch)
    (acceptance.smooth epoch)
    (acceptance.nondegenerate epoch)
    (acceptance.densityIntegrable epoch)
    (acceptance.fullActionStationary epoch)

/-- The complete source-relative integrated Ward law is likewise derived
for every accepted family member. -/
theorem LegacyClassicalWorldAcceptance.integratedSourceRelativeP286Ward
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι) :
    LegacyIntegratedSourceRelativeP286Ward source (family epoch) :=
  smooth_nondegenerate_integrable_implies_legacyIntegratedSourceRelativeP286Ward
    source (family epoch)
    (acceptance.smooth epoch)
    (acceptance.nondegenerate epoch)
    (acceptance.densityIntegrable epoch)

/-- Gravity Bianchi is an off-shell structural identity derived from the
smooth accepted actual. -/
theorem LegacyClassicalWorldAcceptance.gravityBianchi
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantMixedCurvatureDerivative (family epoch) point first second third +
        covariantMixedCurvatureDerivative (family epoch) point second third
          first +
        covariantMixedCurvatureDerivative (family epoch) point third first
          second = 0 :=
  smooth_implies_gravityBianchi (family epoch) (acceptance.smooth epoch)
    point first second third

/-- P286 Bianchi is the corresponding off-shell structural identity. -/
theorem LegacyClassicalWorldAcceptance.p286GaugeBianchi
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantCurvatureDerivative (family epoch) point first second third +
        covariantCurvatureDerivative (family epoch) point second third first +
        covariantCurvatureDerivative (family epoch) point third first second =
      0 :=
  smooth_implies_p286GaugeBianchi (family epoch) (acceptance.smooth epoch)
    point first second third

/-- The accepted P286 action equation reads out the same-actual BF/scalar/
matter current balance. -/
theorem LegacyClassicalWorldAcceptance.p286SectorBalance
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι)
    (direction : P286GaugeOneForm)
    (point : BasePoint) :
    p286GaugeBFBalanceCoefficient (family epoch) direction point +
        p286ScalarCurrentCoefficient source (family epoch) direction point +
        p286MatterCurrentCoefficient source (family epoch) direction point =
      0 :=
  canonicalP286GaugeConnectionActionStationary_generates_sectorBalance
    source (family epoch)
    (acceptance.smooth epoch)
    (acceptance.nondegenerate epoch)
    (acceptance.densityIntegrable epoch)
    (acceptance.fullActionStationary epoch).p286GaugeConnection direction point

/-- The accepted Lorentz action equation reads out the same-actual gravity-BF
and matter-spin balance. -/
theorem LegacyClassicalWorldAcceptance.lorentzSectorBalance
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzGravityBFBalanceCoefficient (family epoch) direction point +
        lorentzMatterSpinSourceCoefficient source (family epoch) direction
          point = 0 :=
  canonicalLorentzConnectionActionStationary_generates_sectorBalance
    source (family epoch)
    (acceptance.smooth epoch)
    (acceptance.nondegenerate epoch)
    (acceptance.densityIntegrable epoch)
    (acceptance.fullActionStationary epoch).lorentzConnection direction point

/-- The accepted coframe equation reads out the four-sector stress balance;
no individual action-owned stress sector is forced to vanish. -/
theorem LegacyClassicalWorldAcceptance.coframeSectorBalance
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι) :
    CanonicalCoframeSectorBalance source (family epoch) :=
  canonicalCoframeActionStationaryF_generates_sectorBalance
    source (family epoch)
    (acceptance.smooth epoch)
    (acceptance.nondegenerate epoch)
    (acceptance.densityIntegrable epoch)
    (acceptance.fullActionStationary epoch).coframe

/-- Package the accepted family member into the already declared raw-action
zero-fiber domain layer. -/
theorem LegacyClassicalWorldAcceptance.integrableJointShellZeroFiber
    {source : SmoothUnifiedSource}
    {ι : Type u}
    {family : LegacyStageNineCClassicalWorldFamily ι}
    (acceptance : LegacyClassicalWorldAcceptance source family)
    (epoch : ι) :
    CurrentIntegrableJointShellZeroFiber source (family epoch) where
  smooth := acceptance.smooth epoch
  nondegenerate := acceptance.nondegenerate epoch
  gravityConnectionLorentzAdmissible :=
    acceptance.gravityConnectionLorentzAdmissible epoch
  densityIntegrable := acceptance.densityIntegrable epoch
  zeroFiber := acceptance.jointShellZeroFiber epoch

/-! ## Current repaired-root single-actual key -/

/-- The dynamic scalar is source-rooted at the canonical contact.  This is a
contact equality on the current field, not a whole-spacetime static-vacuum
claim and not a scalar value supplied to a writer. -/
def DynamicScalarSourceContactAtOrigin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : Prop :=
  current.scalar 0 = generatedLocalVacuumCoordinates source 0 0

/-- The six nonzero physical departments of one current.  The dynamic scalar
contact is deliberately separate: it is provenance for this same current,
not a seventh nonzero sector and not a constant-field constraint. -/
structure SimultaneousSixPhysicalSectorNonzero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : Prop where
  gravityCurvature :
    ∃ point, holonomicGravityCurvature current point ≠ 0
  p286GaugeCurvature :
    ∃ point, holonomicGaugeCurvature current point ≠ 0
  breakingVacuum :
    sourceGeneratedVacuumBase source ≠ 0
  yukawaMass :
    exteriorYukawaMassMap (sourceGeneratedVacuumBase source) ≠ 0
  matterCurrent :
    ∃ point, MatterCurrentNonzeroAt source current point
  stressOrSpin :
    ∃ point, StressOrSpinNonzeroAt source current point

/-- The unique current S9-C key.  It is a dependent acceptance face of one
already fixed root current.  It is not a family selector, writer, root, lock,
or completed future state. -/
structure ClassicalWorldAcceptance
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : Prop where
  smooth : current.Smooth
  nondegenerate : current.Nondegenerate
  gravityConnectionLorentzAdmissible :
    GravityConnectionLorentzAdmissible current
  jointZeroFiber : DiracDualFormNativeJointZeroFiber source current
  dynamicScalarSourceContact :
    DynamicScalarSourceContactAtOrigin source current
  simultaneousSixPhysicalSectorNonzero :
    SimultaneousSixPhysicalSectorNonzero source current

/-- Pointwise elimination of the one authoritative repaired-root residual
field. -/
theorem ClassicalWorldAcceptance.pointwiseJointZeroFiber
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (acceptance : ClassicalWorldAcceptance source current)
    (point : BasePoint) :
    OnDiracDualFormNativePointwiseJointZeroFiber source current point :=
  (diracDualFormNativeJointZeroFiber_iff_pointwise source current).1
    acceptance.jointZeroFiber point

/-- Gravity Bianchi remains a structural readout of current smoothness. -/
theorem ClassicalWorldAcceptance.gravityBianchi
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (acceptance : ClassicalWorldAcceptance source current)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantMixedCurvatureDerivative current point first second third +
        covariantMixedCurvatureDerivative current point second third first +
        covariantMixedCurvatureDerivative current point third first second =
      0 :=
  smooth_implies_gravityBianchi current acceptance.smooth point first second
    third

/-- P286 Bianchi likewise remains an off-shell smoothness readout. -/
theorem ClassicalWorldAcceptance.p286GaugeBianchi
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (acceptance : ClassicalWorldAcceptance source current)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantCurvatureDerivative current point first second third +
        covariantCurvatureDerivative current point second third first +
        covariantCurvatureDerivative current point third first second = 0 :=
  smooth_implies_p286GaugeBianchi current acceptance.smooth point first second
    third

/-! ## One-way legacy projection -/

/-- A legacy witness can forget its obsolete whole-field scalar clause and
supply exactly the six physical departments.  There is intentionally no
converse. -/
theorem LegacySimultaneousSixSectorNonzero.toPhysicalSectors
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (legacy : LegacySimultaneousSixSectorNonzero source current) :
    SimultaneousSixPhysicalSectorNonzero source current where
  gravityCurvature := legacy.gravityCurvature
  p286GaugeCurvature := legacy.p286GaugeCurvature
  breakingVacuum := legacy.breakingVacuum
  yukawaMass := legacy.yukawaMass
  matterCurrent := legacy.matterCurrent
  stressOrSpin := legacy.stressOrSpin

end

end SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance
