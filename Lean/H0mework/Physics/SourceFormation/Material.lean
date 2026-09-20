import H0mework.Physics.SourceFamily.Acceptance

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineCClassicalWorldAcceptance StageNineDiracDualFormNativeJointResidualCarrier
open Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

def index (source : SmoothUnifiedSource) : ℕ := source.stageEight.sigmaSeed

theorem source_coupling (source : SmoothUnifiedSource) :
    source.legacy.sigma = SourceFamily.coupling (index source) := by
  rw [SourceFamily.coupling_value]
  rfl

def seed (source : SmoothUnifiedSource) : StageNineHolonomicConfiguration :=
  { SourceFamily.seedAt (index source) with scalar := fun _ => sourceGeneratedVacuumCoordinates source }

def formedField (source : SmoothUnifiedSource) : StageNineHolonomicConfiguration :=
  algebraicCartanReduction source (seed source)

theorem seed_smooth (source : SmoothUnifiedSource) : (seed source).Smooth := by
  obtain ⟨coframe, connection, auxiliary, multiplier, gauge, gaugeAuxiliary, _, matter, dual⟩ :=
    SourceFamily.seed_smooth (index source)
  exact ⟨coframe, connection, auxiliary, multiplier, gauge, gaugeAuxiliary, contDiff_const, matter, dual⟩

theorem seed_nondegenerate (source : SmoothUnifiedSource) : (seed source).Nondegenerate :=
  SourceFamily.seed_nondegenerate (index source)

theorem field_smooth (source : SmoothUnifiedSource) : (formedField source).Smooth :=
  algebraicCartanReduction_smooth source _ (seed_smooth source) (seed_nondegenerate source)

theorem field_nondegenerate (source : SmoothUnifiedSource) : (formedField source).Nondegenerate :=
  algebraicCartanReduction_nondegenerate source _ (seed_nondegenerate source)

theorem lorentz_admissible (source : SmoothUnifiedSource) :
    StageNineGravityBianchi.GravityConnectionLorentzAdmissible (formedField source) :=
  algebraicCartanReduction_lorentzAdmissible source _ (seed_nondegenerate source)

theorem algebraic_channels (source : SmoothUnifiedSource) (point : BasePoint) :
    let residual := diracDualFormNativePointwiseJointResidual source (formedField source) point
    residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
      residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 :=
  ⟨algebraicCartanReduction_gravityMultiplier_zero _ _ point,
    algebraicCartanReduction_gravityAuxiliary_zero _ _ point,
    algebraicCartanReduction_p286Auxiliary_zero _ _ (seed_nondegenerate source) point,
    algebraicCartanReduction_lorentz_zero _ _ (seed_smooth source) (seed_nondegenerate source) point⟩

theorem field_original : formedField Runtime.source = Runtime.configuration := by
  change algebraicCartanReduction (SourceFamily.sourceAt 0) (SourceFamily.seedAt 0) = _
  exact SourceFamily.field_zero

theorem field_family (step : ℕ) : formedField (SourceFamily.sourceAt step) = SourceFamily.fieldAt step := by
  have index_eq : index (SourceFamily.sourceAt step) = step := SourceFamily.source_seed step
  unfold formedField seed
  rw [index_eq]
  rfl

theorem zero_phase_vacuum_obligation (current : StageNineHolonomicConfiguration)
    (acceptance : ClassicalWorldAcceptance zeroPhaseSmoothUnifiedSource current) : False := by
  exact acceptance.simultaneousSixPhysicalSectorNonzero.breakingVacuum
    zeroPhase_sourceGeneratedVacuumBase

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation
