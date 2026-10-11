import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCoefficientPrice

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedEffective
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal
open SourcePropagationNativeActionHessian CanonicalGradedSpatialSource
open PreparationVacuumCurrentSignalOperator PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalFeedback SourcePropagationConstrainedPoleReturn
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalJacobi originalChange originalInverse originalReadback originalRowLift
  activeKernel kernelFrame nativeHessian sourceAxisCosource sourceAxisClearedField



example (time space : ℂ) :
    blockProjection*activeKernel (planeMomentum time space)=activeKernel (planeMomentum time space)*blockProjection :=
  block_source_commutes time space

example (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : blockProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    effectiveKernel p*ᵥblockCoordinates field=effectiveReader p*ᵥforcing :=
  effective_actual_equation p field forcing inside equation

example (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : blockProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    field=effectiveFrame p*ᵥblockCoordinates field+complementGreen p*ᵥforcing :=
  effective_field_reconstruction p field forcing inside equation

example (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ)
    (regular : planeMomentum time (Complex.I*(momentum:ℂ))∈complementRegular) :
    effectiveKernel ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
      blockCoordinates (actualBlockField q p momentum left right time T)=
      effectiveReader ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
        actualBlockForcing q p momentum left right time T :=
  actual_effective_dynamics q p momentum left right time T regular

example (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ)
    (regular : planeMomentum time (Complex.I*(momentum:ℂ))∈complementRegular) :
    blockComplement (planeMomentum time (Complex.I*(momentum:ℂ))) (actualBlockField q p momentum left right time T)=
      complementGreen ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
        (actualBlockForcing q p momentum left right time T-
          activeKernel (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
            (kernelFrame (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
              blockCoordinates (actualBlockField q p momentum left right time T))) :=
  actual_complement_return q p momentum left right time T regular

example (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ)
    (regular : planeMomentum time (Complex.I*(momentum:ℂ))∈complementRegular) :
    originalChange (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥactualBlockField q p momentum left right time T=
      nativeEffectiveFrame ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
        blockCoordinates (actualBlockField q p momentum left right time T)+
      originalChange (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
        (complementGreen ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
          actualBlockForcing q p momentum left right time T) :=
  actual_native_reconstruction q p momentum left right time T regular

#print axioms block_source_commutes
#print axioms effective_actual_equation
#print axioms effective_field_reconstruction
#print axioms actual_effective_dynamics
#print axioms actual_complement_return
#print axioms actual_native_reconstruction
end LowEnergy.PreparationVacuumMixedEffective
