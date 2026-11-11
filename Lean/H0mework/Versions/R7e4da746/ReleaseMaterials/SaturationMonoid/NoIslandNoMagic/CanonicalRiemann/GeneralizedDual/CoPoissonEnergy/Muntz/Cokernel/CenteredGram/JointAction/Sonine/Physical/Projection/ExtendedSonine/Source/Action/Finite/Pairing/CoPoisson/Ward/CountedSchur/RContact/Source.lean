import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.LogProfile
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource.UnitTailActionSource

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
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "T" => burnolTateReciprocalL2
local notation "F" => fourierL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M := IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private sum_profile from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.SourceJet
open private return_forward return_reverse return_realizes from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.LogProfile
open private inverse_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanAction
open private forward_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDual

def inverseCoefficient (k i:ℕ) : ℂ :=
  (k.choose i:ℂ)*(Real.log q:ℂ)^(k-i)*(-1:ℂ)^i/(k.factorial:ℂ)

/-- This finite basis transport reads the same original divided-log columns; it creates no actor. -/
theorem divided_source (c:BurnolCompletedMellinCoordinate) (k:ℕ) :
    dividedLogColumn c k=∑i∈Finset.range (k+1),inverseCoefficient k i • SourceJet.rawColumn c i := by
  have right:=sum_profile (Finset.range (k+1)) (inverseCoefficient k) (SourceJet.rawColumn c)
    (SourceJet.rawProfile c) (fun i _=>SourceJet.rawColumn_profile c i)
  apply Lp.ext
  filter_upwards [dividedLogColumn_profile c k,right,ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
    with x leftRead rightRead nonzero
  rw [leftRead,rightRead]
  unfold dividedLogRaw
  rw [Real.log_div (by norm_num:q≠0) (abs_ne_zero.mpr nonzero),Complex.ofReal_sub,
    sub_eq_add_neg,add_comm (Real.log q:ℂ),add_pow,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold inverseCoefficient SourceJet.rawProfile
  rw [neg_pow]
  ring

theorem first_basis (c:BurnolCompletedMellinCoordinate) (k:ℕ) :
    logBFirst c k=∑i∈Finset.range (k+1),inverseCoefficient k i • SourceJet.first c i := by
  unfold logBFirst centeredLogColumn
  rw [divided_source]
  simp only [map_sum,map_smul,SourceJet.first,SourceJet.column]

def dividedForward (c:BurnolCompletedMellinCoordinate) (k:ℕ) : BurnolL2 :=
  ∑i∈Finset.range (k+1),inverseCoefficient k i • LogProfile.firstProgramme c i
def dividedReverse (c:BurnolCompletedMellinCoordinate) (k:ℕ) : BurnolL2 :=
  ∑i∈Finset.range (k+1),inverseCoefficient k i • LogProfile.firstReverseProgramme c i

private theorem divided_forward_tendsto (c:BurnolCompletedMellinCoordinate) (k:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (logBFirst c k:Hq))) atTop (𝓝 (dividedForward c k)) := by
  have parts:=tendsto_finsetSum (Finset.range (k+1)) (fun i _=>
    (LogProfile.actual_first_forward c i).const_smul (inverseCoefficient k i))
  apply parts.congr'
  filter_upwards with N
  rw [first_basis]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,←CountingDual.sourceCLM_apply]
private theorem divided_reverse_tendsto (c:BurnolCompletedMellinCoordinate) (k:ℕ) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (logBFirst c k:Hq))) atTop (𝓝 (dividedReverse c k)) := by
  have parts:=tendsto_finsetSum (Finset.range (k+1)) (fun i _=>
    (LogProfile.actual_first_reverse c i).const_smul (inverseCoefficient k i))
  apply parts.congr'
  filter_upwards with N
  rw [first_basis]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,CountingDual.dual_eq_adjoint]

def fieldFirst (c:BurnolCompletedMellinCoordinate) (j:ℕ) : M :=
  burnolAmbientMeanZeroFirstCorrection (sourceField c j)
def fieldForward (c:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  ∑k∈Finset.range j,sourceCoefficient c j k • dividedForward c k
def fieldReverse (c:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  ∑k∈Finset.range j,sourceCoefficient c j k • dividedReverse c k

theorem field_forward_tendsto (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (fieldFirst c j:Hq))) atTop (𝓝 (fieldForward c j)) := by
  have parts:=tendsto_finsetSum (Finset.range j) (fun k _=>
    (divided_forward_tendsto c k).const_smul (sourceCoefficient c j k))
  apply parts.congr'
  filter_upwards with N
  rw [fieldFirst,source_B_first]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,←CountingDual.sourceCLM_apply]
theorem field_reverse_tendsto (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (fieldFirst c j:Hq))) atTop (𝓝 (fieldReverse c j)) := by
  have parts:=tendsto_finsetSum (Finset.range j) (fun k _=>
    (divided_reverse_tendsto c k).const_smul (sourceCoefficient c j k))
  apply parts.congr'
  filter_upwards with N
  rw [fieldFirst,source_B_first]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,CountingDual.dual_eq_adjoint]

private theorem field_even (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    reflectRestricted q (fieldFirst c j:Hq)=fieldFirst c j := by
  rw [fieldFirst,source_B_first]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact congrArg (fun v:M=>(v:Hq)) (log_B_even c k)

private theorem step_dilation (c:BurnolCompletedMellinCoordinate) (shift:ℝ) (value:BurnolL2) :
    sourceStep c (burnolMultiplicativeDilation shift value)=burnolMultiplicativeDilation shift (sourceStep c value) := by
  have inverse:T (burnolMultiplicativeDilation shift value)=burnolMultiplicativeDilation (-shift) (T value) := by
    simpa only [neg_neg] using (burnolTateReciprocalL2_dilation_inverse (-shift) value).symm
  change T (burnolDirectRightResolvent ((barC c).value/2) (T (burnolMultiplicativeDilation shift value)))=
    burnolMultiplicativeDilation shift (T (burnolDirectRightResolvent ((barC c).value/2) (T value)))
  rw [inverse,burnolDirectRightResolvent_dilation,burnolTateReciprocalL2_dilation_inverse]

private theorem step_channel (c:BurnolCompletedMellinCoordinate) (sign a:ℝ) (value:BurnolL2) :
    ContinuousChannels.channel sign a (sourceStep c value)=sourceStep c (ContinuousChannels.channel sign a value) := by
  simp only [ContinuousChannels.channel,map_smul,step_dilation]

private theorem forward_step (N:ℕ) (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    FiniteForcing.source N (sourceStep c value)=sourceStep c (FiniteForcing.source N value) := by
  have integer (n:ℕ):Channels.sourceChannel n (sourceStep c value)=sourceStep c (Channels.sourceChannel n value) := by
    simpa only [Channels.sourceChannel,ContinuousChannels.channel,neg_one_mul] using step_channel c (-1) n value
  unfold FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer,step_channel]
  rw [map_sub,map_sum]
  congr 1
  exact (sourceStep c).integral_comp_comm (ContinuousChannels.channel_integrable (-1) N value)
private theorem reverse_step (N:ℕ) (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    DualSource.source N (sourceStep c value)=sourceStep c (DualSource.source N value) := by
  unfold DualSource.source
  simp_rw [step_channel]
  rw [map_sub,map_sum]
  congr 1
  exact (sourceStep c).integral_comp_comm (ContinuousChannels.channel_integrable 1 N value)

private theorem full_step_supported (c:BurnolCompletedMellinCoordinate) (state:Hq) :
    E (quarterStep c state)=sourceStep c (E state) := by
  have cutoff:(FiniteMobiusResolventFlux.cutoff q) (E state)=E state := by
    change E (Rq (E state))=E state
    rw [burnolQuarterRestriction_zeroExtension]
  have right:1/4<((barC c).value/2).re := by
    rw [Complex.div_re]
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_def,conj_re]
    norm_num
    linarith [c.rightHalf]
  have support:=OriginalPrimitiveRankBalance.cutoff_Rplus_source q (by norm_num)
    ((barC c).value/2) right (E state)
  rw [cutoff,FiniteMobiusResolventFlux.Rplus_tate _ right] at support
  exact support

private theorem centered_step_source (c:BurnolCompletedMellinCoordinate) (state:M) :
    E (centeredQuarterStep c state:Hq)=sourceStep c (E (state:Hq))-
      burnolQuarterMeanCoefficient (quarterStep c (state:Hq)) • ConstantDual.seed := by
  change E (Constructor.zeroMean (quarterStep c (state:Hq)):Hq)=_
  rw [Constructor.zeroMean_read,map_sub,map_smul,full_step_supported]
  rfl

def contactField (c:BurnolCompletedMellinCoordinate) (j:ℕ) : M := BI (finiteContactAction c j)
def contactAmplitude (c:BurnolCompletedMellinCoordinate) (j:ℕ) : ℂ := sourceAmplitude c j-2*finiteMeanContact c j
def contactMean (c:BurnolCompletedMellinCoordinate) (j:ℕ) : ℂ :=
  burnolQuarterMeanCoefficient (quarterStep c (fieldFirst c j:Hq))

/-- The coupled six-contact source is solved by the actual adjacent Jordan fields and the original power unit. -/
theorem contact_source (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    E (contactField c j:Hq)=sourceStep c (E (fieldFirst c j:Hq))-
      contactMean c j • ConstantDual.seed+contactAmplitude c j • E (logBFirst c 0:Hq)-E (fieldFirst c (j+1):Hq) := by
  have native:=actual_B_source_contact_step c j
  change fieldFirst c (j+1)=centeredQuarterStep c (fieldFirst c j)+
    contactAmplitude c j • logBFirst c 0-contactField c j at native
  have solved:contactField c j=centeredQuarterStep c (fieldFirst c j)+
      contactAmplitude c j • logBFirst c 0-fieldFirst c (j+1) := by linear_combination (norm:=module) native
  have complete:=congrArg (fun v:M=>E (v:Hq)) solved
  simp only [Submodule.coe_sub,Submodule.coe_add,Submodule.coe_smul,map_sub,map_add,map_smul] at complete
  rw [centered_step_source] at complete
  exact complete

theorem contact_forward_finite (N:ℕ) (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    FiniteForcing.source N (E (contactField c j:Hq))=
      sourceStep c (FiniteForcing.source N (E (fieldFirst c j:Hq)))-
      contactMean c j • FiniteForcing.source N ConstantDual.seed+
      contactAmplitude c j • FiniteForcing.source N (E (logBFirst c 0:Hq))-
      FiniteForcing.source N (E (fieldFirst c (j+1):Hq)) := by
  rw [contact_source]
  simp only [←CountingDual.sourceCLM_apply,map_sub,map_add,map_smul]
  simp only [CountingDual.sourceCLM_apply,forward_step]

theorem contact_reverse_finite (N:ℕ) (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    DualSource.source N (E (contactField c j:Hq))=
      sourceStep c (DualSource.source N (E (fieldFirst c j:Hq)))-
      contactMean c j • DualSource.source N ConstantDual.seed+
      contactAmplitude c j • DualSource.source N (E (logBFirst c 0:Hq))-
      DualSource.source N (E (fieldFirst c (j+1):Hq)) := by
  rw [contact_source]
  simp only [CountingDual.dual_eq_adjoint,map_sub,map_add,map_smul]
  simp only [←CountingDual.dual_eq_adjoint,reverse_step]

def contactForwardProgramme (c:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  sourceStep c (fieldForward c j)-contactMean c j • ConstantForward.value+
    contactAmplitude c j • dividedForward c 0-fieldForward c (j+1)
def contactReverseProgramme (c:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  sourceStep c (fieldReverse c j)-contactMean c j • ConstantDual.value+
    contactAmplitude c j • dividedReverse c 0-fieldReverse c (j+1)

theorem contact_forward_tendsto (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (contactField c j:Hq))) atTop (𝓝 (contactForwardProgramme c j)) := by
  have generated:=((((sourceStep c).continuous.tendsto _).comp (field_forward_tendsto c j)).sub
    (ConstantForward.original_tendsto.const_smul (contactMean c j))).add
      ((divided_forward_tendsto c 0).const_smul (contactAmplitude c j)) |>.sub (field_forward_tendsto c (j+1))
  exact generated.congr' (Eventually.of_forall (fun N=>(contact_forward_finite N c j).symm))
theorem contact_reverse_tendsto (c:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (contactField c j:Hq))) atTop (𝓝 (contactReverseProgramme c j)) := by
  have generated:=((((sourceStep c).continuous.tendsto _).comp (field_reverse_tendsto c j)).sub
    (ConstantDual.original_tendsto.const_smul (contactMean c j))).add
      ((divided_reverse_tendsto c 0).const_smul (contactAmplitude c j)) |>.sub (field_reverse_tendsto c (j+1))
  exact generated.congr' (Eventually.of_forall (fun N=>(contact_reverse_finite N c j).symm))

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.RContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
