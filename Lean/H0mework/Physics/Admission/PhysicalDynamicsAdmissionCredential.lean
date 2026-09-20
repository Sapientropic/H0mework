import H0mework.Physics.Source.UnifiedPhysicalMasterAction

/-!
# Dependency-light physical dynamics admission credential

This module packages the dependency-light Stage 4 physical responsibility
chain.  It does not add fields to the proof-free source.  Instead, a credential is
constructed after the source has generated its anchor, phase/H1 trace,
sigma, color field, anholonomic geometry, physical `II+` bivector,
torsion-free spin data, non-Abelian curvature, and source-relative stationary
configuration.  Its action provenance is the unified finite master action
which also contains the three empirical first-order gauge sectors.

The credential has no P459/P508/P523 representation-incidence field and no
one-loop running field.  A measured reference-scale coupling boundary remains
a separate explicit argument; it is retained as empirical data and is never
computed from a beta coefficient.  Reference-SM running is packaged only in
the independent `ReferenceSMRunningReceipt` module.
-/

namespace SaturationMonoid.PhysicsCore.PhysicalUnifiedAdmission

open ProofFreeRicherAnholonomicSource
open PhysicalIIPlusFrechetVariation
open JetLocalPhysicalPlebanskiAction
open SourceGeneratedPhysicalPlebanskiConfiguration
open SourceRelativePhysicalStationaryFamily
open UnifiedPhysicalMasterAction
open EmpiricalReferenceScaleCouplingBoundary
open SU7RicherLineageResponsibility
open StandardModelConstraint

noncomputable section

/-- One output record with one immutable rich anchor shared by its geometry
and empirical gauge block.  It intentionally has no incidence-running slot. -/
structure SourceGeneratedPhysicalDynamicsOutput
    (source : Source)
    (boundary : EmpiricalReferenceScaleCouplings) where
  anchor : SourcePhaseFieldAnchor
  geometry : GeneratedOriginGeometry source
  empiricalBoundary : EmpiricalReferenceScaleCouplings
  gaugeBlock : StandardModelGaugeConstitutiveBlock ℝ LorentzianTwoForm

def sourceGeneratedPhysicalDynamicsOutput
    (source : Source)
    (boundary : EmpiricalReferenceScaleCouplings) :
    SourceGeneratedPhysicalDynamicsOutput source boundary where
  anchor := source.anchor
  geometry := generatedOriginGeometry source
  empiricalBoundary := boundary
  gaugeBlock := gaugeConstitutiveBlock boundary

/-- Dependency-light physical dynamics credential.  Every data-bearing copy
is pinned to a computed source output by an exact equality.  No final
credential is accepted by `Source` itself. -/
structure PhysicalDynamicsAdmissionCredential
    (source : Source)
    (boundary : EmpiricalReferenceScaleCouplings) where
  output : SourceGeneratedPhysicalDynamicsOutput source boundary
  output_eq : output = sourceGeneratedPhysicalDynamicsOutput source boundary
  anchor_generated : output.anchor = source.anchor
  phaseTrace_generated :
    output.anchor.phaseCochain = source.phaseCochain
  phaseTrace_nontrivial :
    output.anchor.phaseCochain (Sum.inl ThreeCycleTime.t0)
        (Sum.inl ThreeCycleTime.t1) ≠ 0
  h1_closed : ComponentH1Closed output.anchor.phaseCochain
  sigma_generated : output.anchor.sigma = source.sigma
  sigma_pos : 0 < output.anchor.sigma
  sigma_lt_one : output.anchor.sigma < 1
  field_generated : output.anchor.field = source.field
  field_traceExact : ColorLoopTraceExact output.anchor.field
  field_nonzero : output.anchor.field ≠ 0
  geometry_generated : output.geometry = generatedOriginGeometry source
  geometry_nondegenerate : Matrix.det output.geometry.jet.coframe ≠ 0
  geometry_anholonomic : source.IsAnholonomic
  physicalIIPlus_nonzero : output.geometry.physicalBivector ≠ 0
  action_tetrad_nondegenerate :
    Matrix.det (coframeOfTetradVector
      (sourceStationaryConfiguration source).tetrad) ≠ 0
  action_simplicity :
    JetLocalPhysicalPlebanskiAction.deltaPhi
      (sourceStationaryConfiguration source) = 0
  action_torsionFree :
    PointwiseLorentzianCoframeJet.TorsionFree
      (source.geometryAtOrigin).spin.affineConnection
  action_curvature_generated :
    nonAbelianCurvature (sourceStationaryConfiguration source).connection =
      sourceCurvatureVector source
  all_four_variations_genuine :
    HasFDerivAt
        (fun connection =>
          unifiedMasterAction source boundary
            ((sourceUnifiedConfiguration source).withGravityConnection
              connection))
        (SourceRelativePhysicalStationaryFamily.deltaOmega source
          (sourceStationaryConfiguration source))
        (sourceStationaryConfiguration source).connection ∧
      HasFDerivAt
        (fun bivector =>
          unifiedMasterAction source boundary
            ((sourceUnifiedConfiguration source).withGravityBivector
              bivector))
        (SourceRelativePhysicalStationaryFamily.deltaB source
          (sourceStationaryConfiguration source))
        (sourceStationaryConfiguration source).bivector ∧
      HasFDerivAt
        (fun multiplier =>
          unifiedMasterAction source boundary
            ((sourceUnifiedConfiguration source).withGravityMultiplier
              multiplier))
        (SourceRelativePhysicalStationaryFamily.deltaPhi source
          (sourceStationaryConfiguration source))
        (sourceStationaryConfiguration source).multiplier ∧
      HasFDerivAt
        (fun tetrad =>
          unifiedMasterAction source boundary
            ((sourceUnifiedConfiguration source).withGravityTetrad tetrad))
        (SourceRelativePhysicalStationaryFamily.deltaE source
          (sourceStationaryConfiguration source))
        (sourceStationaryConfiguration source).tetrad
  source_stationary : PhysicalStationaryAtSource source
  unified_source_stationary :
    UnifiedPhysicalStationaryAtSource source boundary
  gauge_auxiliary_elimination :
    (∀ q : GaugeSectorConfiguration,
      gaugeSectorConstitutiveVariation
          boundary.strongCouplingSquared q = 0 ↔
        q.auxiliary =
          (gaugeConstitutiveOperatorVector
            boundary.strongCouplingSquared).symm q.curvature) ∧
    (∀ q : GaugeSectorConfiguration,
      gaugeSectorConstitutiveVariation
          boundary.weakCouplingSquared q = 0 ↔
        q.auxiliary =
          (gaugeConstitutiveOperatorVector
            boundary.weakCouplingSquared).symm q.curvature) ∧
    (∀ q : GaugeSectorConfiguration,
      gaugeSectorConstitutiveVariation
          boundary.hyperchargeCouplingSquared q = 0 ↔
        q.auxiliary =
          (gaugeConstitutiveOperatorVector
            boundary.hyperchargeCouplingSquared).symm q.curvature)
  empiricalBoundary_preserved : output.empiricalBoundary = boundary
  empiricalGaugeBlock_generated :
    output.gaugeBlock = gaugeConstitutiveBlock boundary

def physicalDynamicsAdmissionCredentialOf
    (source : Source)
    (boundary : EmpiricalReferenceScaleCouplings)
    (hphase : source.phaseAmplitude ≠ 0)
    (hfield : source.field ≠ 0)
    (hanholonomic : source.IsAnholonomic)
    (hphysical :
      physicalIIPlusBivector (source.jetAt 0).coframe ≠ 0) :
    PhysicalDynamicsAdmissionCredential source boundary where
  output := sourceGeneratedPhysicalDynamicsOutput source boundary
  output_eq := rfl
  anchor_generated := rfl
  phaseTrace_generated := rfl
  phaseTrace_nontrivial := source.phaseCochain_nontrivial hphase
  h1_closed := source.phaseCochain_h1Closed
  sigma_generated := rfl
  sigma_pos := source.sigma_pos
  sigma_lt_one := source.sigma_lt_one
  field_generated := rfl
  field_traceExact := source.field_traceExact
  field_nonzero := hfield
  geometry_generated := rfl
  geometry_nondegenerate := source.jetAt_zero_nondegenerate
  geometry_anholonomic := hanholonomic
  physicalIIPlus_nonzero := hphysical
  action_tetrad_nondegenerate :=
    sourceActionConfiguration_tetrad_nondegenerate source
  action_simplicity := sourceActionConfiguration_simplicity source
  action_torsionFree := sourceActionConfiguration_torsionFree source
  action_curvature_generated :=
    sourceActionConfiguration_curvature_generated source
  all_four_variations_genuine :=
    unified_all_four_gravity_variations_from_one_action source boundary
      (sourceUnifiedConfiguration source)
  source_stationary := source_generates_stationaryFamily source
  unified_source_stationary :=
    source_generates_unifiedStationaryFamily source boundary
  gauge_auxiliary_elimination :=
    ⟨gaugeSectorConstitutiveVariation_eq_zero_iff_eliminated
        boundary.strongCouplingSquared,
      gaugeSectorConstitutiveVariation_eq_zero_iff_eliminated
        boundary.weakCouplingSquared,
      gaugeSectorConstitutiveVariation_eq_zero_iff_eliminated
        boundary.hyperchargeCouplingSquared⟩
  empiricalBoundary_preserved := rfl
  empiricalGaugeBlock_generated := rfl

theorem positiveSource_physicalIIPlus_nonzero :
    physicalIIPlusBivector (positiveSource.jetAt 0).coframe ≠ 0 := by
  simpa using physicalIIPlusBivector_not_zero

def positivePhysicalDynamicsAdmissionCredential :
    PhysicalDynamicsAdmissionCredential positiveSource unitBoundary :=
  physicalDynamicsAdmissionCredentialOf positiveSource unitBoundary
    (by norm_num [positiveSource])
    positiveSource_field_nonzero
    positiveSource_anholonomic
    positiveSource_physicalIIPlus_nonzero

theorem positiveSource_generates_PhysicalDynamicsAdmissionCredential :
    Nonempty
      (PhysicalDynamicsAdmissionCredential positiveSource unitBoundary) :=
  ⟨positivePhysicalDynamicsAdmissionCredential⟩

theorem credential_retains_exact_responsibility
    {source : Source}
    {boundary : EmpiricalReferenceScaleCouplings}
    (credential : PhysicalDynamicsAdmissionCredential source boundary) :
    credential.output.anchor = source.anchor ∧
      credential.output.geometry = generatedOriginGeometry source ∧
      credential.output.empiricalBoundary = boundary ∧
    credential.output.gaugeBlock = gaugeConstitutiveBlock boundary := by
  rw [credential.output_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Empirical reference-scale data remain an explicit boundary input.  The
light credential contains no map from finite beta arithmetic to this input. -/
theorem empirical_coupling_boundaries_are_distinct_inputs :
    unitBoundary ≠ doubleBoundary ∧
      gaugeConstitutiveBlock unitBoundary ≠
        gaugeConstitutiveBlock doubleBoundary :=
  ⟨unitBoundary_ne_doubleBoundary, gaugeBlocks_distinct⟩

/-! ## Compatibility aliases

The old Stage-4 names remain available while downstream code migrates.  They
alias only the dependency-light credential; no reference-running field is
reintroduced.
-/

abbrev SourceGeneratedUnifiedPhysicalOutput :=
  SourceGeneratedPhysicalDynamicsOutput

abbrev sourceGeneratedUnifiedPhysicalOutput :=
  sourceGeneratedPhysicalDynamicsOutput

abbrev PhysicalUnifiedAdmissionCredential :=
  PhysicalDynamicsAdmissionCredential

abbrev physicalUnifiedAdmissionCredentialOf :=
  physicalDynamicsAdmissionCredentialOf

abbrev positivePhysicalUnifiedAdmissionCredential :=
  positivePhysicalDynamicsAdmissionCredential

theorem positiveSource_generates_PhysicalUnifiedAdmissionCredential :
    Nonempty
      (PhysicalUnifiedAdmissionCredential positiveSource unitBoundary) :=
  positiveSource_generates_PhysicalDynamicsAdmissionCredential

end
end SaturationMonoid.PhysicsCore.PhysicalUnifiedAdmission
