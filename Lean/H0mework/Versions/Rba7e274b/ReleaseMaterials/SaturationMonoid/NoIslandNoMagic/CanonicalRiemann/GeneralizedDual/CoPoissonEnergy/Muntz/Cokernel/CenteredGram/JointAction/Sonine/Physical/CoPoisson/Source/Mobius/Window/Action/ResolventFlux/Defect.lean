import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Reverse
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceReturn.Consumer
import H0mework.Versions.V2.Arithmetic.RieszSynthesis.WholeRead
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set
open scoped InnerProductSpace

def D : BurnolL2 →L[ℂ] BurnolL2 := M.comp fourierL2.toLinearIsometry.toContinuousLinearMap-burnolTateReciprocalL2.comp M

theorem defect_source_physical (value : Ambient) : D (value : BurnolL2)=OriginalRieszFiniteSynthesis.sourceFourierDefect value := by
  unfold D OriginalRieszFiniteSynthesis.sourceFourierDefect
  simp only [sub_apply,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
  have physicalFourier : (evenFaceFourierEquiv burnolUnscaledCommonGapRadius value : BurnolL2)=fourierL2 (value : BurnolL2) := rfl
  rw [← physicalFourier,lower_source_physical,lower_source_physical]

def defectFlux (z : ℂ) (value : BurnolL2) : BurnolL2 := reverseFlux z (fourierL2 value)-burnolTateReciprocalL2 (actualFlux z value)

-- Every term is a complete actual source action; no Pa membership or target cancellation is supplied.
theorem actual_defect_R_action (z : ℂ) (rightQuarter : 1/4<z.re) (value : BurnolL2) :
    D (burnolDirectRightResolvent z value)=Rplus z (D value)+defectFlux z value := by
  unfold D defectFlux
  simp only [sub_apply,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
  rw [fourier_R z rightQuarter,actual_M_Rplus_action z rightQuarter,actual_M_R_action z rightQuarter,
    map_add,tate_R z rightQuarter,Rplus_sub z rightQuarter]
  module

namespace Prior
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
  (coordinate coordinate_value originalK)
end Prior
namespace Return
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceReturn
  (sourceInput returnedField source_return_corrected_field)
end Return
namespace S
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceBalance
  (contactCorrection correctedField regularSource)
end S
namespace P
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction (R)
end P
namespace Paid
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalRAction
  (original_R_direct parameter_rightQuarter)
end Paid
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def sourceA : ℂ := (star observation.coordinate-observation.coordinate)/2
def primitiveSource : BurnolL2 := S.contactCorrection (Prior.coordinate observation nontrivial half)-
  sourceA observation • P.R observation nontrivial half (S.contactCorrection (Prior.coordinate observation nontrivial half))+
  (1/2:ℂ) • P.R observation nontrivial half (S.regularSource (Prior.coordinate observation nontrivial half))

theorem original_return_source_equation : sourceA observation • P.R observation nontrivial half (Prior.originalK observation nontrivial half)-
    Prior.originalK observation nontrivial half=primitiveSource observation nontrivial half := by
  have source := Return.source_return_corrected_field observation nontrivial half
  change P.R observation nontrivial half (Return.sourceInput observation nontrivial half)=_ at source
  unfold Return.sourceInput S.correctedField at source
  rw [map_sub,map_smul,map_add,map_smul,smul_add] at source
  unfold primitiveSource
  have sourceMoved := source
  change sourceA observation • P.R observation nontrivial half (Prior.originalK observation nontrivial half)+
      sourceA observation • P.R observation nontrivial half (S.contactCorrection (Prior.coordinate observation nontrivial half))-
      (1/2:ℂ) • P.R observation nontrivial half (S.regularSource (Prior.coordinate observation nontrivial half)) =
      Prior.originalK observation nontrivial half+S.contactCorrection (Prior.coordinate observation nontrivial half) at sourceMoved
  calc
    _ = (sourceA observation • P.R observation nontrivial half (Prior.originalK observation nontrivial half)+
      sourceA observation • P.R observation nontrivial half (S.contactCorrection (Prior.coordinate observation nontrivial half))-
      (1/2:ℂ) • P.R observation nontrivial half (S.regularSource (Prior.coordinate observation nontrivial half)))+
      (1/2:ℂ) • P.R observation nontrivial half (S.regularSource (Prior.coordinate observation nontrivial half))-
      sourceA observation • P.R observation nontrivial half (S.contactCorrection (Prior.coordinate observation nontrivial half))-
      Prior.originalK observation nontrivial half := by module
    _ = _ := by
      rw [sourceMoved]
      module


-- The literal endpoint primitives and complete finite cutoff flux generate the entire defect forcing.
def defectForcing : BurnolL2 := D (primitiveSource observation nontrivial half)-sourceA observation •
  defectFlux (observation.coordinate/2) (Prior.originalK observation nontrivial half)

theorem original_defect_source_equation : sourceA observation • Rplus (observation.coordinate/2)
      (D (Prior.originalK observation nontrivial half))-D (Prior.originalK observation nontrivial half)=
    defectForcing observation nontrivial half := by
  have source := congrArg D (original_return_source_equation observation nontrivial half)
  rw [map_sub,map_smul,Paid.original_R_direct,actual_defect_R_action _ (Paid.parameter_rightQuarter observation half),smul_add] at source
  unfold defectForcing
  rw [← source]
  module

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
