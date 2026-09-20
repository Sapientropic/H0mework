import H0mework.Physics.Holonomic.HolonomicField

/-!
# S9-C3h85: source-generated holonomic phase evolution

The enriched proof-free source already generates an actual continuous
one-parameter unitary flow.  This module lets that flow act on the primitive
Stage-9 holonomic configuration before any joint residual is read:

* the generated circle element is embedded in the existing P286 hypercharge
  subgroup;
* scalar and Dirac matter fields transform by their actual finite SU(7)
  representations;
* the conjugate matter field transforms by the contragredient action;
* gravity, gauge-connection, and auxiliary fields are fixed by this phase
  evolution.

The resulting configuration update has identity and composition laws, is
nontrivial for the positive source, and collapses to the identity for the
zero-rate source.  It reads no joint-shell residual, keep operator, trace,
target configuration, or response witness.

This is a genuine source-generated internal phase evolution on the full
primitive carrier.  It is not yet the interacting BF/GR/SM evolution: the
gravity and gauge sectors are fixed, and no residual-transport or
stationarity law is asserted here.  Those are downstream acceptance tests.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceGeneratedHolonomicPhaseEvolution

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open DiracExteriorMatterAction

noncomputable section

/-- The actual SU(7) element sampled from the source-generated continuous
phase dynamics. -/
def sourcePhaseGroupElement
    (source : SmoothUnifiedSource) (time : ℝ) : SU7MotherGroup :=
  embeddedP286HyperchargeElement
    ((generatedUnitaryFlow source).evolve time)

@[simp] theorem sourcePhaseGroupElement_zero
    (source : SmoothUnifiedSource) :
    sourcePhaseGroupElement source 0 = 1 := by
  rw [sourcePhaseGroupElement,
    (generatedUnitaryFlow source).evolve_zero,
    embeddedP286HyperchargeElement_one]

theorem sourcePhaseGroupElement_add
    (source : SmoothUnifiedSource) (first second : ℝ) :
    sourcePhaseGroupElement source (first + second) =
      sourcePhaseGroupElement source first *
        sourcePhaseGroupElement source second := by
  rw [sourcePhaseGroupElement, sourcePhaseGroupElement,
    sourcePhaseGroupElement,
    (generatedUnitaryFlow source).evolve_add,
    embeddedP286HyperchargeElement_mul]

/-- Source-generated continuous phase evolution of every primitive Stage-9
field.  Fixed coordinates are fixed by the dynamics itself; they are not
reconstructed from a residual target. -/
def sourceGeneratedHolonomicPhaseUpdate
    (source : SmoothUnifiedSource) (time : ℝ)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration where
  coframe := configuration.coframe
  gravityConnection := configuration.gravityConnection
  gravityAuxiliary := configuration.gravityAuxiliary
  gravitySimplicityMultiplier := configuration.gravitySimplicityMultiplier
  gaugeConnection := configuration.gaugeConnection
  gaugeAuxiliary := configuration.gaugeAuxiliary
  scalar := fun point =>
    scalarCoordinateAction (sourcePhaseGroupElement source time)
      (configuration.scalar point)
  matter := fun point =>
    diracExteriorMatterGaugeRepresentation
      (sourcePhaseGroupElement source time) (configuration.matter point)
  conjugateMatter := fun point =>
    (configuration.conjugateMatter point).comp
      (diracExteriorMatterGaugeRepresentation
        (sourcePhaseGroupElement source time)⁻¹)

@[simp] theorem sourceGeneratedHolonomicPhaseUpdate_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedHolonomicPhaseUpdate source 0 configuration =
      configuration := by
  apply StageNineHolonomicConfiguration.ext
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · funext point
    simp [sourceGeneratedHolonomicPhaseUpdate]
  · funext point
    change
      diracExteriorMatterGaugeRepresentation
          (sourcePhaseGroupElement source 0)
          (configuration.matter point) =
        configuration.matter point
    rw [sourcePhaseGroupElement_zero, map_one]
    rfl
  · funext point
    apply LinearMap.ext
    intro matter
    change
      configuration.conjugateMatter point
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement source 0)⁻¹ matter) =
        configuration.conjugateMatter point matter
    rw [sourcePhaseGroupElement_zero, inv_one, map_one]
    rfl

theorem sourceGeneratedHolonomicPhaseUpdate_add
    (source : SmoothUnifiedSource) (first second : ℝ)
    (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedHolonomicPhaseUpdate source (first + second) configuration =
      sourceGeneratedHolonomicPhaseUpdate source first
        (sourceGeneratedHolonomicPhaseUpdate source second configuration) := by
  apply StageNineHolonomicConfiguration.ext
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · funext point
    change
      scalarCoordinateAction
          (sourcePhaseGroupElement source (first + second))
          (configuration.scalar point) =
        scalarCoordinateAction (sourcePhaseGroupElement source first)
          (scalarCoordinateAction (sourcePhaseGroupElement source second)
            (configuration.scalar point))
    rw [sourcePhaseGroupElement_add, scalarCoordinateAction_mul]
  · funext point
    change
      diracExteriorMatterGaugeRepresentation
          (sourcePhaseGroupElement source (first + second))
          (configuration.matter point) =
        diracExteriorMatterGaugeRepresentation
          (sourcePhaseGroupElement source first)
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement source second)
            (configuration.matter point))
    rw [sourcePhaseGroupElement_add, map_mul]
    rfl
  · funext point
    apply LinearMap.ext
    intro matter
    change
      configuration.conjugateMatter point
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement source (first + second))⁻¹ matter) =
        configuration.conjugateMatter point
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement source second)⁻¹
            (diracExteriorMatterGaugeRepresentation
              (sourcePhaseGroupElement source first)⁻¹ matter))
    rw [sourcePhaseGroupElement_add, mul_inv_rev, map_mul]
    rfl

/-- The phase evolution leaves the coframe unchanged, so it preserves exactly
the nondegenerate holonomic state domain. -/
theorem sourceGeneratedHolonomicPhaseUpdate_nondegenerate_iff
    (source : SmoothUnifiedSource) (time : ℝ)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration.Nondegenerate
        (sourceGeneratedHolonomicPhaseUpdate source time configuration) ↔
      configuration.Nondegenerate :=
  Iff.rfl

theorem sourceGeneratedHolonomicPhaseUpdate_left_inverse
    (source : SmoothUnifiedSource) (time : ℝ)
    (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedHolonomicPhaseUpdate source (-time)
        (sourceGeneratedHolonomicPhaseUpdate source time configuration) =
      configuration := by
  calc
    sourceGeneratedHolonomicPhaseUpdate source (-time)
        (sourceGeneratedHolonomicPhaseUpdate source time configuration) =
        sourceGeneratedHolonomicPhaseUpdate source (-time + time)
          configuration :=
      (sourceGeneratedHolonomicPhaseUpdate_add source (-time) time
        configuration).symm
    _ = configuration := by simp

theorem sourceGeneratedHolonomicPhaseUpdate_right_inverse
    (source : SmoothUnifiedSource) (time : ℝ)
    (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedHolonomicPhaseUpdate source time
        (sourceGeneratedHolonomicPhaseUpdate source (-time) configuration) =
      configuration := by
  calc
    sourceGeneratedHolonomicPhaseUpdate source time
        (sourceGeneratedHolonomicPhaseUpdate source (-time) configuration) =
        sourceGeneratedHolonomicPhaseUpdate source (time + -time)
          configuration :=
      (sourceGeneratedHolonomicPhaseUpdate_add source time (-time)
        configuration).symm
    _ = configuration := by simp

@[simp] theorem zeroRate_sourcePhaseGroupElement
    (time : ℝ) :
    sourcePhaseGroupElement zeroRateSmoothUnifiedSource time = 1 := by
  change embeddedP286HyperchargeElement
      (Circle.exp
        (zeroRateSmoothUnifiedSource.continuousContactRate * time)) = 1
  rw [zeroRate_continuousContactRate]
  simp [embeddedP286HyperchargeElement_one]

@[simp] theorem zeroRate_sourceGeneratedHolonomicPhaseUpdate
    (time : ℝ) (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedHolonomicPhaseUpdate zeroRateSmoothUnifiedSource time
        configuration =
      configuration := by
  apply StageNineHolonomicConfiguration.ext
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · simp [sourceGeneratedHolonomicPhaseUpdate]
  · funext point
    simp [sourceGeneratedHolonomicPhaseUpdate]
  · funext point
    change
      diracExteriorMatterGaugeRepresentation
          (sourcePhaseGroupElement zeroRateSmoothUnifiedSource time)
          (configuration.matter point) =
        configuration.matter point
    rw [zeroRate_sourcePhaseGroupElement, map_one]
    rfl
  · funext point
    apply LinearMap.ext
    intro matter
    change
      configuration.conjugateMatter point
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement zeroRateSmoothUnifiedSource time)⁻¹
            matter) =
        configuration.conjugateMatter point matter
    rw [zeroRate_sourcePhaseGroupElement, inv_one, map_one]
    rfl

/-- A fixed primitive configuration used only to witness that the generated
positive-source phase action is not the identity endomorphism. -/
def positivePhaseProbeConfiguration : StageNineHolonomicConfiguration where
  coframe := fun _ => 1
  gravityConnection := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeConnection := 0
  gaugeAuxiliary := 0
  scalar := fun _ =>
    sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  matter := 0
  conjugateMatter := 0

theorem positivePhaseProbeConfiguration_smooth :
    positivePhaseProbeConfiguration.Smooth := by
  simp [StageNineHolonomicConfiguration.Smooth,
    positivePhaseProbeConfiguration, contDiff_const]

theorem positivePhaseProbeConfiguration_nondegenerate :
    positivePhaseProbeConfiguration.Nondegenerate := by
  intro point
  simp [positivePhaseProbeConfiguration]

theorem positivePhaseProbeConfiguration_update_smooth :
    (sourceGeneratedHolonomicPhaseUpdate positiveSmoothUnifiedSource 1
      positivePhaseProbeConfiguration).Smooth := by
  simp [StageNineHolonomicConfiguration.Smooth,
    sourceGeneratedHolonomicPhaseUpdate, positivePhaseProbeConfiguration,
    contDiff_const]

theorem positivePhaseProbeConfiguration_update_nondegenerate :
    (sourceGeneratedHolonomicPhaseUpdate positiveSmoothUnifiedSource 1
      positivePhaseProbeConfiguration).Nondegenerate :=
  (sourceGeneratedHolonomicPhaseUpdate_nondegenerate_iff
    positiveSmoothUnifiedSource 1 positivePhaseProbeConfiguration).2
      positivePhaseProbeConfiguration_nondegenerate

/-- Positive regression: the actual source-generated unit-time phase moves a
primitive scalar field, so the full configuration update is not the identity.
-/
theorem positive_sourceGeneratedHolonomicPhaseUpdate_nontrivial :
    sourceGeneratedHolonomicPhaseUpdate positiveSmoothUnifiedSource 1
        positivePhaseProbeConfiguration ≠
      positivePhaseProbeConfiguration := by
  intro updateFixed
  have scalarFixed := congrArg
    (fun configuration : StageNineHolonomicConfiguration =>
      configuration.scalar 0) updateFixed
  have coordinateFixed :
      scalarCoordinateAction
          (sourcePhaseGroupElement positiveSmoothUnifiedSource 1)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    simpa [sourceGeneratedHolonomicPhaseUpdate,
      positivePhaseProbeConfiguration] using scalarFixed
  have baseFixed :
      exteriorBreakingScalarRepresentation
          (sourcePhaseGroupElement positiveSmoothUnifiedSource 1)
          (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) =
        sourceGeneratedVacuumBase positiveSmoothUnifiedSource := by
    have pushed := congrArg scalarCoordinateEquiv.symm coordinateFixed
    simpa [scalarCoordinateAction, sourceGeneratedVacuumCoordinates] using
      pushed
  have phaseFixed :
      (generatedUnitaryFlow positiveSmoothUnifiedSource).evolve 1 = 1 := by
    exact
      (positive_hypercharge_mem_vacuumStabilizer_iff
        ((generatedUnitaryFlow positiveSmoothUnifiedSource).evolve 1)).mp
        baseFixed
  exact positive_generatedUnitaryFlow_nontrivial phaseFixed

end

end SaturationMonoid.PhysicsCore.StageNineSourceGeneratedHolonomicPhaseEvolution
