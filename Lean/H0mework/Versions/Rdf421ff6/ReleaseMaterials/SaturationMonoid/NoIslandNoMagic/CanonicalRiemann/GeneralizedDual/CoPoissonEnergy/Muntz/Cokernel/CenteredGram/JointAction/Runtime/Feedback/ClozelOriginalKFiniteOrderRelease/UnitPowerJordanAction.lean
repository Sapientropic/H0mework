import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.UnitPowerJordanAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open UnitPowerJordanSource
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "B" => burnolMeanZeroOneMinusSquare
local notation "BI" => burnolMeanZeroBlockInverse
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def centeredQuarterStep (c : BurnolCompletedMellinCoordinate) : M →L[ℂ] M :=
  Constructor.zeroMean.comp ((quarterStep c).comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

def meanContact (c : BurnolCompletedMellinCoordinate) (k : Nat) : ℂ :=
  burnolQuarterMeanCoefficient (dividedLogColumn c k) * (q:ℂ)^(1-star c.value)/(1-star c.value)

private theorem centered_constant_step (c : BurnolCompletedMellinCoordinate) :
    Constructor.zeroMean (quarterStep c (intervalConstant q)) =
      (-(2:ℂ)*(q:ℂ)^(1-star c.value)/(1-star c.value)) • SingularCounting.centeredPower c := by
  rw [quarterStep_constant,map_sub,map_smul,map_smul,Constructor.zeroMean_constant,smul_zero,zero_sub]
  change -((2*(q:ℂ)^(1-star c.value)/(1-star c.value)) • SingularCounting.centeredPower c)=_
  rw [←neg_smul]
  congr 1
  ring

/-- The actual Volterra step on the centered log source retains its original constant contact. -/
theorem centered_log_step (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    centeredQuarterStep c (centeredLogColumn c k) =
      (-2:ℂ) • centeredLogColumn c (k+1) + (2*meanContact c k) • centeredLogColumn c 0 := by
  have source := congrArg Constructor.zeroMean (quarterStep_log_column c k)
  rw [map_smul] at source
  have split : dividedLogColumn c k =
      (centeredLogColumn c k:Hq)+burnolQuarterMeanCoefficient (dividedLogColumn c k) • intervalConstant q := by
    unfold centeredLogColumn
    rw [Constructor.zeroMean_read]
    module
  rw [split,map_add,map_smul,map_add,map_smul,centered_constant_step] at source
  change centeredQuarterStep c (centeredLogColumn c k)+
    burnolQuarterMeanCoefficient (dividedLogColumn c k) •
      ((-(2:ℂ)*(q:ℂ)^(1-star c.value)/(1-star c.value)) • SingularCounting.centeredPower c)=
        (-2:ℂ) • centeredLogColumn c (k+1) at source
  change _=(-2:ℂ) • centeredLogColumn c (k+1)+(2*meanContact c k) • SingularCounting.centeredPower c
  unfold meanContact
  linear_combination (norm:=module) source

/-- This is the actual Volterra/Fourier square difference, with the same input on both legs. -/
def quarterCommutator (c : BurnolCompletedMellinCoordinate) (value : M) : M :=
  centeredQuarterStep c (S (S value))-S (S (centeredQuarterStep c value))

private theorem inverse_equation (value : M) : B (BI value)=value := by
  change (B*BI) value=value
  rw [burnolMeanZeroBlockInverse_right]
  rfl

/-- The original B inverse consumes the complete same-input quarter commutator. -/
theorem quarter_inverse_action (c : BurnolCompletedMellinCoordinate) (value : M) :
    centeredQuarterStep c (BI value)=BI (centeredQuarterStep c value)+BI (quarterCommutator c (BI value)) := by
  have balance : B (centeredQuarterStep c (BI value))=
      centeredQuarterStep c value+quarterCommutator c (BI value) := by
    calc
      _ = centeredQuarterStep c (B (BI value))+quarterCommutator c (BI value) := by
        change centeredQuarterStep c (BI value)-S (S (centeredQuarterStep c (BI value)))=
          centeredQuarterStep c (BI value-S (S (BI value)))+
            (centeredQuarterStep c (S (S (BI value)))-S (S (centeredQuarterStep c (BI value))))
        rw [map_sub]
        module
      _ = _ := by rw [inverse_equation]
  have solved := congrArg BI balance
  have left : BI*B=1 := Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  change (BI*B) (centeredQuarterStep c (BI value))=BI _ at solved
  rw [left,map_add] at solved
  exact solved

/-- Every original B/log column generates its next column and the complete mean/commutator feedback. -/
theorem log_B_feedback (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    centeredQuarterStep c (logBFirst c k)=
      (-2:ℂ) • logBFirst c (k+1)+(2*meanContact c k) • logBFirst c 0+
        BI (quarterCommutator c (logBFirst c k)) := by
  change centeredQuarterStep c (BI (centeredLogColumn c k))=_
  rw [quarter_inverse_action,centered_log_step,map_add,map_smul,map_smul]
  rfl

open private zeroMean_raw
  from H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseAction
open private quarter_raw_of_even
  from H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource
open private sourceOneMinusSquare_reflect
  from H0mework.Versions.V2.Arithmetic.RieszForcing.SourceParity

private theorem inverse_even (value : M) (even : sourceMeanZeroReflection value=value) :
    sourceMeanZeroReflection (BI value)=BI value := by
  have actual := sourceOneMinusSquare_reflect (BI value)
  rw [inverse_equation,even] at actual
  have solved := congrArg BI actual
  have left : BI*B=1 := Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  change (BI*B) (sourceMeanZeroReflection (BI value))=BI value at solved
  rw [left] at solved
  exact solved

private theorem centered_log_even (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    sourceMeanZeroReflection (centeredLogColumn c k)=centeredLogColumn c k := by
  apply Subtype.ext
  change reflectRestricted q (burnolQuarterMeanZeroProjection (dividedLogColumn c k))=
    burnolQuarterMeanZeroProjection (dividedLogColumn c k)
  rw [←burnolQuarterMeanZeroProjection_reflect,dividedLogColumn_even]

theorem log_B_even (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    sourceMeanZeroReflection (logBFirst c k)=logBFirst c k := inverse_even _ (centered_log_even c k)

private theorem fourier_even (value : M) (even : sourceMeanZeroReflection value=value) :
    sourceMeanZeroReflection (S value)=S value := by
  have actual := sourceMeanZeroFourier_reflect value
  rw [even] at actual
  exact actual.symm

/-- These are finite source Fourier integrals, not selected point values of a new solution. -/
def logFirstRaw (c : BurnolCompletedMellinCoordinate) (k : Nat) (x : ℝ) : ℂ :=
  InverseAction.centeredRaw (dividedLogRaw c k) x+burnolMeanZeroFourierRaw (S (logBFirst c k)) x

theorem log_first_profile (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    (logBFirst c k:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] logFirstRaw c k := by
  have raw := zeroMean_raw (dividedLogColumn c k) (dividedLogRaw c k) (dividedLogColumn_profile c k)
  have equation := (log_B_source c k).1
  have source : logBFirst c k=centeredLogColumn c k+S (S (logBFirst c k)) := by
    rw [logBSecond,map_neg] at equation
    linear_combination (norm:=module) equation
  rw [source]
  filter_upwards [Lp.coeFn_add (centeredLogColumn c k:Hq) (S (S (logBFirst c k)):Hq),
    raw,burnolMeanZeroFourier_ae_raw (S (logBFirst c k))] with x sumRead input square
  change ((centeredLogColumn c k:Hq)+(S (S (logBFirst c k)):Hq)) x=_
  rw [sumRead]
  change (centeredLogColumn c k:Hq) x+(S (S (logBFirst c k)):Hq) x=_
  change (centeredLogColumn c k:Hq) x=InverseAction.centeredRaw (dividedLogRaw c k) x at input
  exact congrArg₂ (fun a b:ℂ=>a+b) input square

/-- The original finite upper endpoint and lower density power remain literal. -/
def quarterRaw (c : BurnolCompletedMellinCoordinate) (raw : ℝ→ℂ) (x : ℝ) : ℂ :=
  -2*((|x|:ℝ):ℂ)^(star c.value-1)*(∫ t:ℝ in |x|..q,(t:ℂ)^(-star c.value)*raw t)

def centeredQuarterRaw (c : BurnolCompletedMellinCoordinate) (raw : ℝ→ℂ) : ℝ→ℂ :=
  InverseAction.centeredRaw (quarterRaw c raw)

private theorem quarter_profile (c : BurnolCompletedMellinCoordinate) (value : Hq) (raw : ℝ→ℂ)
    (even : reflectRestricted q value=value)
    (represents : (value:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] raw) :
    (quarterStep c value:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] quarterRaw c raw := by
  apply quarter_raw_of_even _ _
    ((quarterStep_reflect c value).trans (congrArg (quarterStep c) even))
    (fun x=>by simp only [quarterRaw,abs_neg])
  have global := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp represents
  filter_upwards [quarterStep_positive_profile c value,ae_restrict_mem (measurableSet_symmetricInterval q)]
    with x profile inside positive
  rw [profile positive]
  unfold quarterRaw
  rw [abs_of_pos positive]
  congr 1
  rw [intervalIntegral.integral_of_le inside.2,intervalIntegral.integral_of_le inside.2]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae global,ae_restrict_mem measurableSet_Ioc] with t input member
  rw [input ⟨by linarith [member.1],member.2⟩]

private theorem centered_quarter_profile (c : BurnolCompletedMellinCoordinate) (value : M) (raw : ℝ→ℂ)
    (even : sourceMeanZeroReflection value=value)
    (represents : (value:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] raw) :
    (centeredQuarterStep c value:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] centeredQuarterRaw c raw :=
  zeroMean_raw _ _ (quarter_profile c (value:Hq) raw (congrArg (fun v:M=>(v:Hq)) even) represents)

/-- Both same-input square legs are calculated by original finite Fourier and Volterra integrals. -/
def logCommutatorRaw (c : BurnolCompletedMellinCoordinate) (k : Nat) (x : ℝ) : ℂ :=
  centeredQuarterRaw c (InverseAction.squareRaw (logFirstRaw c k)) x-
    InverseAction.squareRaw (centeredQuarterRaw c (logFirstRaw c k)) x

theorem log_commutator_profile (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    (quarterCommutator c (logBFirst c k):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] logCommutatorRaw c k := by
  have first := log_first_profile c k
  have square : (S (S (logBFirst c k)):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]
      InverseAction.squareRaw (logFirstRaw c k) := by
    rw [←InverseAction.square_raw _ _ first]
    exact burnolMeanZeroFourier_ae_raw _
  have moved := centered_quarter_profile c (logBFirst c k) (logFirstRaw c k) (log_B_even c k) first
  have firstLeg := centered_quarter_profile c (S (S (logBFirst c k))) _
    (fourier_even _ (fourier_even _ (log_B_even c k))) square
  have secondLeg : (S (S (centeredQuarterStep c (logBFirst c k))):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]
      InverseAction.squareRaw (centeredQuarterRaw c (logFirstRaw c k)) := by
    rw [←InverseAction.square_raw _ _ moved]
    exact burnolMeanZeroFourier_ae_raw _
  exact (Lp.coeFn_sub _ _).trans (firstLeg.sub secondLeg)

theorem log_commutator_memLp (c : BurnolCompletedMellinCoordinate) (k : Nat) :
    MemLp (logCommutatorRaw c k) 2 (volume.restrict (symmetricInterval q)) :=
  (memLp_congr_ae (log_commutator_profile c k)).mp (Lp.memLp (quarterCommutator c (logBFirst c k):Hq))

/-- The same finite source coefficients transport every generated B/log feedback term. -/
theorem finite_B_feedback (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    centeredQuarterStep c (burnolAmbientMeanZeroFirstCorrection (sourceField c j))=
      (∑ k∈Finset.range j,sourceCoefficient c j k •
        ((-2:ℂ) • logBFirst c (k+1)+(2*meanContact c k) • logBFirst c 0))+
      BI (∑ k∈Finset.range j,sourceCoefficient c j k • quarterCommutator c (logBFirst c k)) := by
  rw [source_B_first,map_sum]
  simp only [map_smul,log_B_feedback,smul_add,Finset.sum_add_distrib,map_sum]

private theorem source_B_first_succ (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    burnolAmbientMeanZeroFirstCorrection (sourceField c (j+1))=
      sourceAmplitude c j • logBFirst c 0+
      ∑ k∈Finset.range j,sourceCoefficient c j k • ((-2:ℂ) • logBFirst c (k+1)) := by
  rw [source_B_first,Finset.sum_range_succ',add_comm]
  simp only [sourceCoefficient,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

/-- This mean is generated by every original log column, before any target quarter is read. -/
def finiteMeanContact (c : BurnolCompletedMellinCoordinate) (j : Nat) : ℂ :=
  ∑ k∈Finset.range j,sourceCoefficient c j k*meanContact c k

def finiteCommutator (c : BurnolCompletedMellinCoordinate) (j : Nat) : M :=
  ∑ k∈Finset.range j,sourceCoefficient c j k • quarterCommutator c (logBFirst c k)

def finiteCommutatorRaw (c : BurnolCompletedMellinCoordinate) (j : Nat) (x : ℝ) : ℂ :=
  ∑ k∈Finset.range j,sourceCoefficient c j k*logCommutatorRaw c k x

theorem finite_commutator_profile (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    (finiteCommutator c j:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] finiteCommutatorRaw c j := by
  classical
  have go (s : Finset Nat) :
      ((∑ k∈s,sourceCoefficient c j k • quarterCommutator c (logBFirst c k):M):ℝ→ℂ)=ᵐ[
        volume.restrict (symmetricInterval q)]
          fun x => ∑ k∈s,sourceCoefficient c j k*logCommutatorRaw c k x := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero ℂ 2 _
    | @insert k s outside ih =>
      simp only [Finset.sum_insert outside]
      filter_upwards [Lp.coeFn_add
        ((sourceCoefficient c j k • quarterCommutator c (logBFirst c k):M):Hq)
        ((∑ l∈s,sourceCoefficient c j l • quarterCommutator c (logBFirst c l):M):Hq),
        Lp.coeFn_smul (sourceCoefficient c j k) (quarterCommutator c (logBFirst c k):Hq),
        log_commutator_profile c k,ih] with x sumRead scaled actual remaining
      change (((sourceCoefficient c j k • quarterCommutator c (logBFirst c k):M):Hq)+
        ((∑ l∈s,sourceCoefficient c j l • quarterCommutator c (logBFirst c l):M):Hq)) x=_
      rw [sumRead]
      change ((sourceCoefficient c j k • quarterCommutator c (logBFirst c k):M):Hq) x+
        ((∑ l∈s,sourceCoefficient c j l • quarterCommutator c (logBFirst c l):M):Hq) x=_
      change (sourceCoefficient c j k • (quarterCommutator c (logBFirst c k):Hq):Hq) x+
        ((∑ l∈s,sourceCoefficient c j l • quarterCommutator c (logBFirst c l):M):Hq) x=_
      rw [scaled]
      change sourceCoefficient c j k*(quarterCommutator c (logBFirst c k):Hq) x+
        ((∑ l∈s,sourceCoefficient c j l • quarterCommutator c (logBFirst c l):M):Hq) x=_
      rw [actual,remaining]
  exact go (Finset.range j)

theorem finite_commutator_memLp (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    MemLp (finiteCommutatorRaw c j) 2 (volume.restrict (symmetricInterval q)) :=
  (memLp_congr_ae (finite_commutator_profile c j)).mp (Lp.memLp (finiteCommutator c j:Hq))

/-- The actual next full-adjoint source generates its B-column feedback with the whole mean and commutator. -/
theorem actual_B_source_step (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    burnolAmbientMeanZeroFirstCorrection (sourceField c (j+1))=
      centeredQuarterStep c (burnolAmbientMeanZeroFirstCorrection (sourceField c j))+
      (sourceAmplitude c j-2*finiteMeanContact c j) • logBFirst c 0-
      BI (finiteCommutator c j) := by
  have feedback := finite_B_feedback c j
  simp only [smul_add,Finset.sum_add_distrib] at feedback
  have means : (∑ k∈Finset.range j,sourceCoefficient c j k • ((2*meanContact c k) • logBFirst c 0))=
      (2*finiteMeanContact c j) • logBFirst c 0 := by
    simp only [smul_smul]
    rw [←Finset.sum_smul]
    congr 1
    unfold finiteMeanContact
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [means] at feedback
  rw [source_B_first_succ]
  change _=centeredQuarterStep c (burnolAmbientMeanZeroFirstCorrection (sourceField c j))+
    (sourceAmplitude c j-2*finiteMeanContact c j) • logBFirst c 0-
    BI (∑ k∈Finset.range j,sourceCoefficient c j k • quarterCommutator c (logBFirst c k))
  linear_combination (norm:=module) -feedback

end OriginalKFiniteOrderRelease.UnitPowerJordanAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
