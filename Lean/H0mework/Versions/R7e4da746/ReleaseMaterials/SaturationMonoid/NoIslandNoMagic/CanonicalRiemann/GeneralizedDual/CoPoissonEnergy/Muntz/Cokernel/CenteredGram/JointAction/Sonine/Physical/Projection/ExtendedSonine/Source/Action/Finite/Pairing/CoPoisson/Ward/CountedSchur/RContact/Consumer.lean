import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.RContact.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.RContact
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace BigOperators
open OriginalRieszSource
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKFiniteOrderRelease.QuarterSourceCommutator
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "F" => fourierL2
local instance : CompleteSpace M := IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private field_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.RContact.Source
open private return_forward return_reverse return_realizes from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.LogProfile
open private first_even second_reflection from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.SourceJet
open private extension_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private evenPart_of_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private evenPart_sum evenPart_smul from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource

private theorem centered_step_even (c:BurnolCompletedMellinCoordinate) (value:M)
    (even:reflectRestricted q (value:Hq)=value) :
    reflectRestricted q (centeredQuarterStep c value:Hq)=centeredQuarterStep c value := by
  change reflectRestricted q (burnolQuarterMeanZeroProjection (quarterStep c (value:Hq)))=
    burnolQuarterMeanZeroProjection (quarterStep c (value:Hq))
  rw [←burnolQuarterMeanZeroProjection_reflect,quarterStep_reflect,even]

private theorem contact_even (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    reflectRestricted q (contactField c j:Hq)=contactField c j := by
  have native:=actual_B_source_contact_step c j
  change fieldFirst c (j+1)=centeredQuarterStep c (fieldFirst c j)+
    contactAmplitude c j • logBFirst c 0-contactField c j at native
  have solved:contactField c j=centeredQuarterStep c (fieldFirst c j)+
    contactAmplitude c j • logBFirst c 0-fieldFirst c (j+1) := by linear_combination (norm:=module) native
  have powerParity:reflectRestricted q (logBFirst c 0:Hq)=logBFirst c 0 :=
    congrArg (fun v:M=>(v:Hq)) (log_B_even c 0)
  rw [solved]
  simp only [Submodule.coe_sub,Submodule.coe_add,Submodule.coe_smul,map_sub,map_add,map_smul,
    centered_step_even c _ (field_even c j),field_even,powerParity]

/-- The other foot is the actual Fourier response of this already generated six-contact field. -/
theorem contact_second_forward (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (-(S (contactField c j)):Hq))) atTop
      (𝓝 (-LogProfile.returnProgramme (contactField c j))) := by
  have actual:=(return_forward (contactField c j) (contact_even c j)).neg
  apply actual.congr'
  filter_upwards with N
  simp only [map_neg,←CountingDual.sourceCLM_apply]

theorem contact_second_reverse (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (-(S (contactField c j)):Hq))) atTop
      (𝓝 (-OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired.poissonPair
        (LogProfile.returnProgramme (contactField c j)))) := by
  have actual:=(return_reverse (contactField c j) (contact_even c j)).neg
  apply actual.congr'
  filter_upwards with N
  simp only [map_neg,CountingDual.dual_eq_adjoint]

private theorem second_basis (c:BurnolCompletedMellinCoordinate) (k:ℕ) :
    logBSecond c k=∑i∈Finset.range (k+1),inverseCoefficient k i • SourceJet.second c i := by
  rw [logBSecond,first_basis,map_sum]
  simp only [map_smul,SourceJet.second,Finset.sum_neg_distrib,smul_neg]
private theorem whole_wave_even (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    reflectL2 (SourceJet.wholeWave c j)=SourceJet.wholeWave c j := by
  rw [SourceJet.wholeWave,map_add,←fourierL2_reflectL2_commute,
    extension_even _ (first_even c j),extension_even _ (second_reflection c j)]
private theorem outside_column_basis (c:BurnolCompletedMellinCoordinate) (k:ℕ) :
    logOutsideColumn c k=∑i∈Finset.range (k+1),inverseCoefficient k i • SourceJet.wholeWave c i := by
  unfold logOutsideColumn
  rw [first_basis,second_basis]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
  rw [←Finset.sum_add_distrib]
  simp_rw [←smul_add]
  change burnolAmbientEvenPart (∑i∈Finset.range (k+1),inverseCoefficient k i • SourceJet.wholeWave c i)=_
  rw [evenPart_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [evenPart_smul,evenPart_of_even _ (whole_wave_even c i)]

def outsideFinite (c:BurnolCompletedMellinCoordinate) (j N:ℕ) : BurnolL2 :=
  ∑k∈Finset.range j,sourceCoefficient c j k •
    (∑i∈Finset.range (k+1),inverseCoefficient k i • FiniteForcing.source N (SourceJet.wholeWave c i))
def outsideProgramme (c:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  ∑k∈Finset.range j,sourceCoefficient c j k •
    (∑i∈Finset.range (k+1),inverseCoefficient k i • LogProfile.waveProgramme c i)

/-- Every old source coefficient consumes the full same-column wave, including both means and spatial outside. -/
theorem outside_finite (N:ℕ) (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    FiniteForcing.source N (sourceOutside c j)=outsideFinite c j N := by
  unfold sourceOutside outsideFinite
  simp_rw [outside_column_basis]
  simp only [←CountingDual.sourceCLM_apply,map_sum,map_smul]

theorem outside_tendsto (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (sourceOutside c j)) atTop (𝓝 (outsideProgramme c j)) := by
  have parts:=tendsto_finsetSum (Finset.range j) (fun k _=>
    (tendsto_finsetSum (Finset.range (k+1)) (fun i _=>
      (LogProfile.actual_wave_tendsto c i).const_smul (inverseCoefficient k i))).const_smul (sourceCoefficient c j k))
  exact parts.congr' (Eventually.of_forall (fun N=>(outside_finite N c j).symm))

namespace MaterialConsumer
namespace Native
export OriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer (MaterialAt actual_unit_jordan_on_original_whole_next)
end Native
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal N:ℕ)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "Hcurrent" => OriginalKFiniteOrderRelease.UnitPowerSource.fulladjointPowerZ observation half
local notation "Pcurrent" => (OriginalKFiniteOrderRelease.UnitPowerSource.paPowerField observation half:BurnolL2)
local notation "Qcurrent" => OriginalKFiniteOrderRelease.UnitPowerJordanSource.sourceQ observation half
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal

private theorem whole_price (original:Native.MaterialAt observation nontrivial half depth ordinal) :
    inner ℂ (FiniteForcing.source N Qcurrent) raw=
      inner ℂ (FiniteForcing.source N Hcurrent) raw-inner ℂ (FiniteForcing.source N Pcurrent) raw-
      inner ℂ (outsideFinite c m N) raw := by
  have current:=congrArg (fun value:BurnolL2=>inner ℂ (FiniteForcing.source N value) raw) original.sourceInventory
  simp only [←CountingDual.sourceCLM_apply,map_add,inner_add_left] at current
  simp only [CountingDual.sourceCLM_apply,outside_finite] at current
  linear_combination -current

/-- An independent read retains the original MaterialAt/whole-next and consumes this new source effect. -/
noncomputable def read :=
  let original:=Native.actual_unit_jordan_on_original_whole_next observation nontrivial half depth ordinal
  let contact:=contactField c (m-1)
  PProd.mk original <| PProd.mk contact <| PProd.mk
    (PProd.mk (contact_source c (m-1)) (PProd.mk (contact_forward_finite N c (m-1)) (contact_reverse_finite N c (m-1)))) <|
    PProd.mk (PProd.mk (contact_forward_tendsto c (m-1)) (PProd.mk (contact_reverse_tendsto c (m-1))
      (PProd.mk (contact_second_forward c (m-1)) (contact_second_reverse c (m-1))))) <|
    PProd.mk (PProd.mk (outside_finite N c m) (outside_tendsto c m)) <|
    PProd.mk (whole_price observation nontrivial half depth ordinal N original)
      (PProd.mk original.firstBSource (PProd.mk original.secondBSource (PProd.mk original.rawPrice
        (PProd.mk original.bornPrice original.inherited.generatedIndex))))

end MaterialConsumer

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.RContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
