import H0mework.Physics.MotherDeclarationsPhysical.LawsCompletion
import H0mework.NavierStokes.SourceAction.SourceView.Formation.Occurrence.Fields

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherOccurrenceMaterial
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.Stage10.SourceUniqueness
noncomputable section
variable {nu : Viscosity}
variable {seed : GeneratedWholeRestartCurrent nu}

def side (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : MotherStreamLaws.Stream
  | 0 => currentCode seed input.1.1
  | 1 => input.2.time
  | 2 => input.2.radius
  | 3 => input.2.order
  | _ => 0

def nsRawInput (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : MotherPhysicalLaws.Input :=
  ((rawState seed input.1,sourceClock seed input.1.1),side seed input)

theorem nsRawInput_injective (seed : GeneratedWholeRestartCurrent nu) : Function.Injective (nsRawInput seed) := by
  rintro ⟨⟨first,firstOccurrence⟩,firstQuery⟩ ⟨⟨last,lastOccurrence⟩,lastQuery⟩ same
  have sideSame:side seed (⟨first,firstOccurrence⟩,firstQuery)=side seed (⟨last,lastOccurrence⟩,lastQuery):=
    congrArg Prod.snd same
  have currents:first=last := currentCode_injective seed (Nat.cast_injective (congrFun sideSame 0))
  cases currents
  have values:observation seed ⟨first,firstOccurrence⟩=observation seed ⟨first,lastOccurrence⟩ := by
    funext parameter index
    have actual:=congrArg (fun input : MotherPhysicalLaws.Input => input.1.1.coframe (samplePoint parameter index) 0 0) same
    simpa only [nsRawInput,rawState_read] using actual
  have occurrences:firstOccurrence=lastOccurrence:=occurrence_recovered seed first firstOccurrence lastOccurrence values
  have query:firstQuery=lastQuery := by
    cases firstQuery with
    | mk firstTime firstRadius firstOrder =>
      cases lastQuery with
      | mk lastTime lastRadius lastOrder =>
        have ht:firstTime=lastTime:=congrFun sideSame 1
        have hr:firstRadius=lastRadius:=Nat.cast_injective (congrFun sideSame 2)
        have ho:firstOrder=lastOrder:=Nat.cast_injective (congrFun sideSame 3)
        cases ht
        cases hr
        cases ho
        rfl
  cases occurrences
  cases query
  rfl

local instance nonemptyInput (seed : GeneratedWholeRestartCurrent nu) : Nonempty (Input seed) :=
  ⟨(⟨.finite 0,nativeTemporalEmitted seed (.finite 0)⟩,⟨0,0,0⟩)⟩

def recover (seed : GeneratedWholeRestartCurrent nu) : MotherPhysicalLaws.Input → Input seed :=
  Function.invFun (nsRawInput seed)

theorem recover_nsRawInput (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    recover seed (nsRawInput seed input)=input :=
  Function.leftInverse_invFun (nsRawInput_injective seed) input

theorem raw_formed (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    ∃ law : MotherPointwiseLaws.Law,MotherRawCurrent.readCurrent law=(nsRawInput seed input).1 := by
  obtain ⟨law,_,formed⟩:=MotherRawCurrent.every_current (nsRawInput seed input).1
  exact ⟨law,formed⟩

theorem input_formed (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    ∃ law : MotherPointwiseLaws.Law,∃ side : MotherStreamFormation.Carrier,
      (MotherRawCurrent.readCurrent law,MotherStreamFormation.read side)=nsRawInput seed input ∧
        recover seed (MotherRawCurrent.readCurrent law,MotherStreamFormation.read side)=input := by
  obtain ⟨law,raw⟩:=raw_formed seed input
  obtain ⟨side,query⟩:=MotherStreamFormation.read_surjective (nsRawInput seed input).2
  have actual:(MotherRawCurrent.readCurrent law,MotherStreamFormation.read side)=nsRawInput seed input:=Prod.ext raw query
  exact ⟨law,side,actual,actual ▸ recover_nsRawInput seed input⟩

end
end SaturationMonoid.NavierStokes.NativeWindowMotherOccurrenceMaterial
