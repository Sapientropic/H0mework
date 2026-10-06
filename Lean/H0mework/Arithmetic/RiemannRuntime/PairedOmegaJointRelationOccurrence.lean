import H0mework.Arithmetic.RiemannRuntime.PairedOmegaJointScaleFaces

/-!
# Full paired-Omega joint relation occurrence

The actual orbit ambient and the installed balance carrier form one canonical
additive biproduct.  Joint-action atoms live in the first summand; the
already generated phase/retained/trace atoms live in the second.  No detector
value is lifted back into the orbit carrier.

At every compiler stage seven independent source relations are exposed:

* `sourceSeed - sourceActionSeed - sourceBoundary`;
* `evolvedSeed - sourceActionSeed - incidence`;
* their quarter-scale source-boundary sibling;
* their quarter-scale incidence sibling;
* the canonical energy/remainder decomposition of the quarter boundary;
* the quarter-scale `phase - retained - centeredTrace` effect projection;
* `phase - retained - centeredTrace`.

The first retains the before/after integral source boundary.  The second is
the defining equation of the actual `Omega` incidence; the third is the
installed root-effect conservation law.  The first two q-rich faces meet on
the same installed retained atom without identifying their integral faces.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open SourceGeneratedIntegralCoherentJointAction
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation
open Character.GlobalCoPoissonCurrent

noncomputable section

/-- Canonical biproduct of the full joint state and its installed accounting
balance.  The second summand is not a chosen section of the first. -/
abbrev PairedOmegaJointRelationCarrier :=
  PairedOmegaJointAmbient × QRich.ClozelJPair

inductive RuntimeJointRelationRole
  | sourceSeed
  | evolvedSeed
  | sourceActionSeed
  | sourceBoundary
  | incidence
  | quarterSourceSeed
  | quarterEvolvedSeed
  | quarterSourceActionSeed
  | quarterSourceBoundary
  | quarterBoundaryEnergy
  | quarterBoundaryRemainder
  | quarterIncidence
  | quarterPhase
  | quarterRetained
  | quarterCenteredTrace
  | phase
  | retained
  | centeredTrace
  deriving DecidableEq

abbrev RuntimeJointRelationGenerator := Nat × RuntimeJointRelationRole

def runtimeJointRelationAtom
    (stage : Nat) (role : RuntimeJointRelationRole) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  Finsupp.single (stage, role) 1

def runtimeJointStateInclusion :
    PairedOmegaJointAmbient →ₗ[ℤ] PairedOmegaJointRelationCarrier where
  toFun := fun state => (state, 0)
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp

def runtimeJointBalanceInclusion :
    QRich.ClozelJPair →ₗ[ℤ] PairedOmegaJointRelationCarrier where
  toFun := fun balance => (0, balance)
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp

def runtimeJointIntegralFace :
    PairedOmegaJointRelationCarrier →ₗ[ℤ] IntegralScaleCarrier where
  toFun := fun state => state.1.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def runtimeJointCoherentFace :
    PairedOmegaJointRelationCarrier →ₗ[ℤ]
      (JointGraphTarget × JointGraphTarget) where
  toFun := fun state => state.1.2.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Both q-rich coordinates are observations of the same biproduct. -/
def runtimeJointMeasurementFace :
    PairedOmegaJointRelationCarrier →ₗ[ℤ] QRich.ClozelJPair where
  toFun := fun state => state.1.2.2 + state.2
  map_add' := by
    intro left right
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  map_smul' := by
    intro coefficient state
    simp [smul_add]

def runtimeJointBalanceFace :
    PairedOmegaJointRelationCarrier →ₗ[ℤ] QRich.ClozelJPair where
  toFun := Prod.snd
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def runtimeJointRelationGeneratorValue
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RuntimeJointRelationGenerator → PairedOmegaJointRelationCarrier
  | (stage, .evolvedSeed) =>
      runtimeJointStateInclusion
        (runtimeJointEvolvedAmbientAt observation nontrivial stage)
  | (stage, .sourceSeed) =>
      runtimeJointStateInclusion
        (runtimeJointSourceSeedAmbientAt observation nontrivial stage)
  | (stage, .sourceActionSeed) =>
      runtimeJointStateInclusion
        (runtimeJointSourceActionAmbientAt observation nontrivial stage)
  | (stage, .sourceBoundary) =>
      runtimeJointStateInclusion
        (runtimeJointSourceBoundaryAmbientAt observation nontrivial stage)
  | (stage, .incidence) =>
      runtimeJointStateInclusion
        (runtimeJointIncidenceAmbientAt observation nontrivial stage)
  | (stage, .quarterEvolvedSeed) =>
      runtimeJointStateInclusion
        (runtimeJointQuarterEvolvedAmbientAt observation nontrivial stage)
  | (stage, .quarterSourceSeed) =>
      runtimeJointStateInclusion
        (runtimeJointQuarterSourceSeedAmbientAt observation nontrivial stage)
  | (stage, .quarterSourceActionSeed) =>
      runtimeJointStateInclusion
        (runtimeJointQuarterSourceActionAmbientAt
          observation nontrivial stage)
  | (stage, .quarterSourceBoundary) =>
      runtimeJointStateInclusion
        (runtimeJointQuarterSourceBoundaryAmbientAt
          observation nontrivial stage)
  | (stage, .quarterBoundaryEnergy) =>
      runtimeJointStateInclusion
        (runtimeJointQuarterBoundaryEnergyAmbientAt
          observation nontrivial stage)
  | (stage, .quarterBoundaryRemainder) =>
      runtimeJointStateInclusion
        (runtimeJointQuarterBoundaryRemainderAmbientAt
          observation nontrivial stage)
  | (stage, .quarterIncidence) =>
      runtimeJointStateInclusion
        (runtimeJointQuarterIncidenceAmbientAt observation nontrivial stage)
  | (stage, .quarterPhase) =>
      runtimeJointBalanceInclusion
        (runtimeJointQuarterPhaseAt observation nontrivial stage)
  | (stage, .quarterRetained) =>
      runtimeJointBalanceInclusion
        (runtimeJointQuarterRetainedAt observation nontrivial stage)
  | (stage, .quarterCenteredTrace) =>
      runtimeJointBalanceInclusion
        (runtimeJointQuarterCenteredTraceAt observation nontrivial stage)
  | (stage, .phase) =>
      runtimeJointBalanceInclusion
        (installedRuntimeEffectValueAt observation nontrivial stage).phase
  | (stage, .retained) =>
      runtimeJointBalanceInclusion
        (installedRuntimeEffectValueAt observation nontrivial stage).retained
  | (stage, .centeredTrace) =>
      runtimeJointBalanceInclusion
        (installedRuntimeEffectValueAt observation nontrivial stage).centeredTrace

def runtimeJointRelationEvaluator
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (RuntimeJointRelationGenerator →₀ ℤ) →ₗ[ℤ]
      PairedOmegaJointRelationCarrier :=
  (Finsupp.liftAddHom fun generator =>
    AddMonoidHom.flip (smulAddHom ℤ PairedOmegaJointRelationCarrier)
      (runtimeJointRelationGeneratorValue observation nontrivial generator)
    ).toIntLinearMap

def runtimeJointIncidenceStageRelation (stage : Nat) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  runtimeJointRelationAtom stage .evolvedSeed -
    runtimeJointRelationAtom stage .sourceActionSeed -
      runtimeJointRelationAtom stage .incidence

def runtimeJointSourceBoundaryStageRelation (stage : Nat) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  runtimeJointRelationAtom stage .sourceSeed -
    runtimeJointRelationAtom stage .sourceActionSeed -
      runtimeJointRelationAtom stage .sourceBoundary

def runtimeJointQuarterIncidenceStageRelation (stage : Nat) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  runtimeJointRelationAtom stage .quarterEvolvedSeed -
    runtimeJointRelationAtom stage .quarterSourceActionSeed -
      runtimeJointRelationAtom stage .quarterIncidence

def runtimeJointQuarterSourceBoundaryStageRelation (stage : Nat) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  runtimeJointRelationAtom stage .quarterSourceSeed -
    runtimeJointRelationAtom stage .quarterSourceActionSeed -
      runtimeJointRelationAtom stage .quarterSourceBoundary

/-- The actual quarter source boundary is written once as its canonical
energy coordinate plus the complementary integral/measurement remainder. -/
def runtimeJointQuarterBoundaryEnergyStageRelation (stage : Nat) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  runtimeJointRelationAtom stage .quarterSourceBoundary -
    runtimeJointRelationAtom stage .quarterBoundaryEnergy -
      runtimeJointRelationAtom stage .quarterBoundaryRemainder

def runtimeJointQuarterBalanceStageRelation (stage : Nat) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  runtimeJointRelationAtom stage .quarterPhase -
    runtimeJointRelationAtom stage .quarterRetained -
      runtimeJointRelationAtom stage .quarterCenteredTrace

def runtimeJointBalanceStageRelation (stage : Nat) :
    RuntimeJointRelationGenerator →₀ ℤ :=
  runtimeJointRelationAtom stage .phase -
    runtimeJointRelationAtom stage .retained -
      runtimeJointRelationAtom stage .centeredTrace

theorem runtimeJointIncidenceStageRelation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointRelationEvaluator observation nontrivial
        (runtimeJointIncidenceStageRelation stage) = 0 := by
  rw [runtimeJointIncidenceStageRelation, map_sub, map_sub]
  simp only [runtimeJointRelationEvaluator, runtimeJointRelationAtom,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.flip_apply, smulAddHom_apply, one_smul]
  apply Prod.ext
  · exact runtimeJointAmbient_incidence_relation
      observation nontrivial stage
  · simp [runtimeJointRelationGeneratorValue, runtimeJointStateInclusion]

theorem runtimeJointSourceBoundaryStageRelation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointRelationEvaluator observation nontrivial
        (runtimeJointSourceBoundaryStageRelation stage) = 0 := by
  rw [runtimeJointSourceBoundaryStageRelation, map_sub, map_sub]
  simp only [runtimeJointRelationEvaluator, runtimeJointRelationAtom,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.flip_apply, smulAddHom_apply, one_smul]
  apply Prod.ext
  · exact runtimeJointAmbient_sourceBoundary_relation
      observation nontrivial stage
  · simp [runtimeJointRelationGeneratorValue, runtimeJointStateInclusion]

theorem runtimeJointQuarterIncidenceStageRelation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointRelationEvaluator observation nontrivial
        (runtimeJointQuarterIncidenceStageRelation stage) = 0 := by
  rw [runtimeJointQuarterIncidenceStageRelation, map_sub, map_sub]
  simp only [runtimeJointRelationEvaluator, runtimeJointRelationAtom,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.flip_apply, smulAddHom_apply, one_smul]
  apply Prod.ext
  · exact runtimeJointQuarterAmbient_incidence_relation
      observation nontrivial stage
  · simp [runtimeJointRelationGeneratorValue, runtimeJointStateInclusion]

theorem runtimeJointQuarterSourceBoundaryStageRelation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointRelationEvaluator observation nontrivial
        (runtimeJointQuarterSourceBoundaryStageRelation stage) = 0 := by
  rw [runtimeJointQuarterSourceBoundaryStageRelation, map_sub, map_sub]
  simp only [runtimeJointRelationEvaluator, runtimeJointRelationAtom,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.flip_apply, smulAddHom_apply, one_smul]
  apply Prod.ext
  · exact runtimeJointQuarterAmbient_sourceBoundary_relation
      observation nontrivial stage
  · simp [runtimeJointRelationGeneratorValue, runtimeJointStateInclusion]

theorem runtimeJointQuarterBoundaryEnergyStageRelation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointRelationEvaluator observation nontrivial
        (runtimeJointQuarterBoundaryEnergyStageRelation stage) = 0 := by
  rw [runtimeJointQuarterBoundaryEnergyStageRelation, map_sub, map_sub]
  simp only [runtimeJointRelationEvaluator, runtimeJointRelationAtom,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.flip_apply, smulAddHom_apply, one_smul]
  apply Prod.ext
  · exact runtimeJointQuarterAmbient_boundaryEnergy_relation
      observation nontrivial stage
  · simp [runtimeJointRelationGeneratorValue, runtimeJointStateInclusion]

theorem runtimeJointQuarterBalanceStageRelation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointRelationEvaluator observation nontrivial
        (runtimeJointQuarterBalanceStageRelation stage) = 0 := by
  rw [runtimeJointQuarterBalanceStageRelation, map_sub, map_sub]
  simp only [runtimeJointRelationEvaluator, runtimeJointRelationAtom,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.flip_apply, smulAddHom_apply, one_smul]
  apply Prod.ext
  · simp [runtimeJointRelationGeneratorValue, runtimeJointBalanceInclusion]
  · change runtimeJointQuarterPhaseAt observation nontrivial stage -
        runtimeJointQuarterRetainedAt observation nontrivial stage -
          runtimeJointQuarterCenteredTraceAt observation nontrivial stage = 0
    rw [runtimeJointQuarterEffect_conservation
      observation nontrivial stage]
    abel

theorem runtimeJointBalanceStageRelation_evaluates_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointRelationEvaluator observation nontrivial
        (runtimeJointBalanceStageRelation stage) = 0 := by
  rw [runtimeJointBalanceStageRelation, map_sub, map_sub]
  simp only [runtimeJointRelationEvaluator, runtimeJointRelationAtom,
    Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.flip_apply, smulAddHom_apply, one_smul]
  apply Prod.ext
  · simp [runtimeJointRelationGeneratorValue, runtimeJointBalanceInclusion]
  · change
      (installedRuntimeEffectValueAt observation nontrivial stage).phase -
          (installedRuntimeEffectValueAt observation nontrivial stage).retained -
        (installedRuntimeEffectValueAt observation nontrivial stage).centeredTrace = 0
    rw [installedRuntimeEffectValueAt_conservation
      observation nontrivial stage]
    abel

def runtimeEffectGeneratorToJointGenerator :
    RuntimeEffectRelationGenerator → RuntimeJointRelationGenerator
  | (stage, .phase) => (stage, .phase)
  | (stage, .retained) => (stage, .retained)
  | (stage, .centeredTrace) => (stage, .centeredTrace)

def runtimeEffectRelationToJointRelation :
    (RuntimeEffectRelationGenerator →₀ ℤ) →ₗ[ℤ]
      (RuntimeJointRelationGenerator →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ runtimeEffectGeneratorToJointGenerator

@[simp] theorem runtimeEffectRelationToJointRelation_stage
    (stage : Nat) :
    runtimeEffectRelationToJointRelation (runtimeEffectStageRelation stage) =
      runtimeJointBalanceStageRelation stage := by
  simp [runtimeEffectRelationToJointRelation,
    runtimeEffectGeneratorToJointGenerator, runtimeEffectStageRelation,
    runtimeJointBalanceStageRelation, runtimeEffectRelationAtom,
    runtimeJointRelationAtom, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_sub]

/-- The old detector evaluator is literally the balance summand of the new
full evaluator. -/
theorem runtimeJointRelationEvaluator_extends_detector
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeJointBalanceFace.comp
        (runtimeJointRelationEvaluator observation nontrivial)).comp
          runtimeEffectRelationToJointRelation =
      runtimeEffectRelationEvaluator observation nontrivial := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  rcases generator with ⟨stage, role⟩
  cases role <;>
    simp [runtimeJointBalanceFace, runtimeJointRelationEvaluator,
      runtimeEffectRelationEvaluator, runtimeEffectRelationToJointRelation,
      runtimeEffectGeneratorToJointGenerator,
      runtimeJointRelationGeneratorValue,
      runtimeEffectRelationGeneratorValue, runtimeJointBalanceInclusion,
      Finsupp.lmapDomain_apply]

/-- The retained field of the installed stage is the same actual incidence
measurement used above. -/
theorem installedRuntimeEffectValueAt_retained_eq_jointIncidence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    (installedRuntimeEffectValueAt observation nontrivial stage).retained =
      pairedOmegaMeasurementResidual observation nontrivial
        (stageSqrtScaleUnit stage) := by
  rw [installedRuntimeEffectValueAt_eq_current]
  simp [generateRuntimeEffect]

/-- The two formerly separate mouths meet on an actual value: measurement
of the joint incidence atom is the installed retained effect. -/
theorem runtimeJointIncidence_measurement_eq_installedRetained
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointMeasurementFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (stage, .incidence)) =
      (installedRuntimeEffectValueAt observation nontrivial stage).retained := by
  change
    (runtimeJointIncidenceAmbientAt observation nontrivial stage).2.2 + 0 =
      (installedRuntimeEffectValueAt observation nontrivial stage).retained
  rw [add_zero]
  change
    pairedOmegaMeasurementResidual observation nontrivial
        (stageSqrtScaleUnit stage) =
      (installedRuntimeEffectValueAt observation nontrivial stage).retained
  exact (installedRuntimeEffectValueAt_retained_eq_jointIncidence
    observation nontrivial stage).symm

/-- With the installed identity measurement action, the nonzero integral
source boundary has the same q-rich read as the vertical incidence. -/
theorem runtimeJointSourceBoundary_measurement_eq_installedRetained
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    runtimeJointMeasurementFace
        (runtimeJointRelationGeneratorValue observation nontrivial
          (stage, .sourceBoundary)) =
      (installedRuntimeEffectValueAt observation nontrivial stage).retained := by
  change
    (runtimeJointInputAt observation nontrivial stage).measurementFace
        ((runtimeJointInputAt observation nontrivial stage).sourceBoundary
          (delta 1)) + 0 = _
  rw [add_zero]
  rw [Input.sourceBoundary_measurement_eq_incidence]
  · change pairedOmegaMeasurementResidual observation nontrivial
        (stageSqrtScaleUnit stage) = _
    exact (installedRuntimeEffectValueAt_retained_eq_jointIncidence
      observation nontrivial stage).symm
  · rfl

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
