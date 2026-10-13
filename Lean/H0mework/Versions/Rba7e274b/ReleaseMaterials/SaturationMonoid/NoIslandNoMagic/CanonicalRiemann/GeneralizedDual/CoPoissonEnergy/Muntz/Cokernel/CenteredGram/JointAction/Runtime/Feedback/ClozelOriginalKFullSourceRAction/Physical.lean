import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRAction.Writeback
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
open Complex MeasureTheory
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
namespace Flux
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux
  (D Rplus defectFlux actual_defect_R_action sourceA primitiveSource original_return_source_equation)
end Flux
namespace SourceR
export OriginalKCombCofinalRAction (original_R_direct parameter_rightQuarter)
end SourceR
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def oldIncrement (ordinal : Nat) : BurnolL2:=
  Prior.inheritedIncrement observation nontrivial half depth ordinal+Prior.actualDelta observation nontrivial half depth ordinal

theorem actual_R_written_source (ordinal : Nat) :
    (actualWriteRead observation nontrivial half depth ordinal).1.1=
      Op.R observation nontrivial half (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half):BurnolL2)+
      Op.R observation nontrivial half (oldIncrement observation nontrivial half depth ordinal)+
      Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal) := by
  rw [actual_R_write_read]
  change Op.R observation nontrivial half (Prior.actualWriteRead observation nontrivial half depth ordinal).1.1+
    Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)=_
  rw [Prior.actual_native_physical_field]
  change Op.R observation nontrivial half ((burnolCompletedMellinRieszVector _:BurnolL2)+_+_)+_=_
  rw [add_assoc,map_add]
  rfl

theorem actual_R_written_defect (ordinal : Nat) :
    (actualWriteRead observation nontrivial half depth ordinal).1.2=
      Flux.D ((actualWriteRead observation nontrivial half depth ordinal).1.1) := by
  rw [actual_R_write_read]
  change Flux.D (Op.R observation nontrivial half (originalField (Prior.actualWriteRead observation nontrivial half depth ordinal)))+
    Flux.D (Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal))=
      Flux.D (_+_)
  exact (map_add _ _ _).symm

/-- The actual complete source is priced by the existing Rplus/flux equation.
The forward R, reverse Rplus and D are never identified or commuted for free. -/
theorem actual_R_defect_flux (ordinal : Nat) :
    (actualWriteRead observation nontrivial half depth ordinal).1.2=
      Flux.Rplus (observation.coordinate/2)
        (Flux.D (originalField (Prior.actualWriteRead observation nontrivial half depth ordinal)))+
      Flux.defectFlux (observation.coordinate/2)
        (originalField (Prior.actualWriteRead observation nontrivial half depth ordinal))+
      Flux.Rplus (observation.coordinate/2)
        (Flux.D (actualDelta observation nontrivial half depth ordinal))+
      Flux.defectFlux (observation.coordinate/2) (actualDelta observation nontrivial half depth ordinal) := by
  rw [actual_R_write_read]
  change Flux.D (Op.R observation nontrivial half (originalField (Prior.actualWriteRead observation nontrivial half depth ordinal)))+
    Flux.D (Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal))=_
  rw [SourceR.original_R_direct,SourceR.original_R_direct,
    Flux.actual_defect_R_action _ (SourceR.parameter_rightQuarter observation half),
    Flux.actual_defect_R_action _ (SourceR.parameter_rightQuarter observation half)]
  module

theorem actual_R_source_equation (ordinal : Nat) :
    Flux.sourceA observation • (actualWriteRead observation nontrivial half depth ordinal).1.1-
      originalField (Prior.actualWriteRead observation nontrivial half depth ordinal)=
      Flux.primitiveSource observation nontrivial half+
      Flux.sourceA observation • Op.R observation nontrivial half (oldIncrement observation nontrivial half depth ordinal)-
      oldIncrement observation nontrivial half depth ordinal+
      Flux.sourceA observation • Op.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal) := by
  have original:=Flux.original_return_source_equation observation nontrivial half
  rw [actual_R_written_source]
  have parent:=Prior.actual_native_physical_field observation nontrivial half depth ordinal
  rw [add_assoc] at parent
  change originalField (Prior.actualWriteRead observation nontrivial half depth ordinal)=
    (burnolCompletedMellinRieszVector _:BurnolL2)+oldIncrement observation nontrivial half depth ordinal at parent
  rw [parent,smul_add,smul_add]
  rw [show Flux.sourceA observation • Op.R observation nontrivial half
    (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half):BurnolL2)=
      Flux.primitiveSource observation nontrivial half+
      (burnolCompletedMellinRieszVector _:BurnolL2) by exact eq_add_of_sub_eq original]
  module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
