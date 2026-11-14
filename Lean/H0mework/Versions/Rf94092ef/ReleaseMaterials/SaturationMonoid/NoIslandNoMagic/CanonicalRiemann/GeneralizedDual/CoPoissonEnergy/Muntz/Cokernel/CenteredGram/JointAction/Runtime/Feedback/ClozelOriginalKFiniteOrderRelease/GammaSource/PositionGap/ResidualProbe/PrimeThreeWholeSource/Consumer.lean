import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.Install
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.Finite
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKConductor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.WidePositionGapAction
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.ShiftedPaCovector

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer
open BurnolPhysicalState OriginalPaPhysicalGreen OriginalKCrossParameterRAdjointSource
open OriginalGamma.Source.KGamma OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.FiniteLogCounting
open scoped InnerProductSpace
namespace CS
export BoundaryNativeKConductorSource (Source physical)
end CS
namespace Recurrence
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence
  (physicalUpdated original_updated_total original_updated_physical_nonzero)
end Recurrence
open private original_decoded from
  H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKAction
open private gap_restrict from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.OutsideHistory.ClockReconstruction
open private dilation_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "D" => burnolMultiplicativeDilation
local notation "K" => burnolCompletedMellinRieszVector

private theorem action_gap {v : BurnolL2} (gap : v ∈ locallyConstantFace 1) :
    Math.action v ∈ locallyConstantFace (Math.scale⁻¹) := by
  have positive : 0 < Math.scale := Real.sqrt_pos.mpr (by norm_num)
  have large : 1 < Math.scale := by
    have square : Math.scale^2=3 := Real.sq_sqrt (by norm_num)
    have nonnegative : 0 ≤ Math.scale := Real.sqrt_nonneg _
    nlinarith
  have first : D Math.shift v ∈ locallyConstantFace Math.scale⁻¹ := by
    simpa only [Math.shift, Real.exp_neg, Real.exp_log positive, one_mul] using
      burnolMultiplicativeDilation_mem_locallyConstantFace_scaled Math.shift gap
  have second : D (-Math.shift) v ∈ locallyConstantFace Math.scale := by
    simpa only [Math.shift, neg_neg, Real.exp_log positive, one_mul] using
      burnolMultiplicativeDilation_mem_locallyConstantFace_scaled (-Math.shift) gap
  have shrink : Math.scale⁻¹ ≤ Math.scale :=
    ((inv_lt_one₀ positive).2 large).le.trans large.le
  exact (locallyConstantFace Math.scale⁻¹).sub_mem
    ((locallyConstantFace Math.scale⁻¹).smul_mem _ first)
    ((locallyConstantFace Math.scale⁻¹).smul_mem _ (gap_restrict shrink second))

private theorem gap_width : (1/4 : ℝ) < Math.scale⁻¹ := by
  have positive : 0 < Math.scale := Real.sqrt_pos.mpr (by norm_num)
  have square : Math.scale^2=3 := Real.sq_sqrt (by norm_num)
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ positive).2
  nlinarith

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ j : Nat, observation.coordinate=-2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "factory" => OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half
local notation "nativeAt" => OriginalKCofinalFullBranchFibre.KernelWrite.originalNative observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

def input (ordinal : Nat) : CS.Source := BoundaryNativeKConductor.inputSource observation nontrivial half depth ordinal

def value (ordinal n : Nat) : BurnolL2 := Install.value c n factory (nativeAt (ordinal+1))

theorem value_source (ordinal n : Nat) : value observation nontrivial half depth ordinal n =
    Math.action (input observation nontrivial half depth ordinal).value :=
  (Install.value_source c n factory (nativeAt (ordinal+1))).trans
    (congrArg Math.action ((original_decoded observation nontrivial half depth ordinal n).trans
      (BoundaryNativeKConductor.input_value observation nontrivial half depth ordinal n).symm))

theorem input_Gram_live (ordinal : Nat) : (input observation nontrivial half depth ordinal).value ≠ 0 := by
  have exactSource : (input observation nontrivial half depth ordinal).value =
      Recurrence.physicalUpdated observation nontrivial half depth ordinal :=
    (Recurrence.original_updated_total observation nontrivial half depth ordinal).symm
  rw [exactSource]
  exact Recurrence.original_updated_physical_nonzero observation nontrivial half depth ordinal

def fullSource (ordinal : Nat) : CS.Source := Math.sourceAction (input observation nontrivial half depth ordinal)

theorem full_source_value (ordinal n : Nat) : (fullSource observation nontrivial half depth ordinal).value =
    value observation nontrivial half depth ordinal n := (value_source observation nontrivial half depth ordinal n).symm

theorem actual_full_log_Gamma (ordinal n : Nat) :
    LogPair (value observation nontrivial half depth ordinal n) (fullSource observation nontrivial half depth ordinal).position ∧
    LogPair (fourierL2.symm (value observation nontrivial half depth ordinal n))
      (fullSource observation nontrivial half depth ordinal).inverse ∧
    GammaPair (value observation nontrivial half depth ordinal n) (fullSource observation nontrivial half depth ordinal).gamma ∧
    (fullSource observation nontrivial half depth ordinal).gamma = Math.action (input observation nontrivial half depth ordinal).gamma := by
  rw [← full_source_value observation nontrivial half depth ordinal n]
  exact ⟨(fullSource observation nontrivial half depth ordinal).position_graph,
    (fullSource observation nontrivial half depth ordinal).inverse_graph,
    (fullSource observation nontrivial half depth ordinal).graph,
    Math.source_action_gamma _⟩

theorem actual_strength (ordinal n : Nat) :
    (Math.weight-Math.weight⁻¹)*‖(input observation nontrivial half depth ordinal).value‖ ≤
      ‖value observation nontrivial half depth ordinal n‖ ∧ value observation nontrivial half depth ordinal n ≠ 0 := by
  rw [value_source]
  exact ⟨Math.lower_bound _,Math.action_live (input_Gram_live observation nontrivial half depth ordinal)⟩

theorem actual_gap (ordinal n : Nat) : value observation nontrivial half depth ordinal n ∈
    locallyConstantFace Math.scale⁻¹ := by
  rw [value_source]
  apply action_gap
  exact (locallyConstantFace 1).sub_mem
    (WidePositionGap.actual_division_unit_position_gap observation nontrivial half depth (ordinal+3))
    (WidePositionGap.actual_division_unit_position_gap observation nontrivial half depth (ordinal+1))

theorem actual_physical_live (ordinal n : Nat) : P (value observation nontrivial half depth ordinal n) ≠ 0 := by
  intro erased
  have even : reflectL2 (value observation nontrivial half depth ordinal n)=value observation nontrivial half depth ordinal n := by
    rw [← full_source_value observation nontrivial half depth ordinal n]
    exact (fullSource observation nontrivial half depth ordinal).even
  exact (actual_strength observation nontrivial half depth ordinal n).2
    (PhysicalClock.physical_read_faithful_on_wider_gap _ gap_width
      (actual_gap observation nontrivial half depth ordinal n) even erased)

def joint (ordinal n : Nat) : BurnolL2 × BurnolL2 :=
  (P (value observation nontrivial half depth ordinal n),O (value observation nontrivial half depth ordinal n))

theorem actual_joint_recovery (ordinal n : Nat) :
    Program.Inverse.operator ((joint observation nontrivial half depth ordinal n).1+
      (joint observation nontrivial half depth ordinal n).2) = (input observation nontrivial half depth ordinal).value ∧
    joint observation nontrivial half depth ordinal n ≠ 0 := by
  have split := OriginalKCombFullResidualAction.split_complete (value observation nontrivial half depth ordinal n)
  constructor
  · change Program.Inverse.operator (P _+O _)=_
    rw [split,value_source]
    exact Program.Inverse.recover _
  · intro erased
    have first := congrArg Prod.fst erased
    exact actual_physical_live observation nontrivial half depth ordinal n first

theorem actual_finite_source (ordinal n N : Nat) :
    originalPhysicalCutoff ((N : ℝ)+1) (value observation nontrivial half depth ordinal n) =
      originalPhysicalCutoff ((N : ℝ)+1) (finitePrimeThreeSourceAction (Finite.sigma (input observation nontrivial half depth ordinal).value) (primeThreeGramCount N)) +
      (((Real.sqrt 3 : ℂ)-(Real.sqrt 3 : ℂ)⁻¹)*Finite.mean (input observation nontrivial half depth ordinal).value) • physicalMeanCell ((N : ℝ)+1) +
      originalPhysicalCutoff ((N : ℝ)+1) (Math.action (Finite.residual (input observation nontrivial half depth ordinal).value)) +
      originalPhysicalCutoff ((N : ℝ)+1) (Math.action (Finite.outside (input observation nontrivial half depth ordinal).value)) := by
  rw [value_source]
  exact Finite.source_action _ N

theorem actual_B_projection (ordinal n : Nat) : P (value observation nontrivial half depth ordinal n) =
    value observation nontrivial half depth ordinal n-burnolAmbientEvenMeanZeroCorrection (value observation nontrivial half depth ordinal n) := by
  have formula := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (value observation nontrivial half depth ordinal n)
  change P (value observation nontrivial half depth ordinal n)=_ at formula
  have even := (fullSource observation nontrivial half depth ordinal).even
  rw [full_source_value observation nontrivial half depth ordinal n] at even
  rw [burnolAmbientExtendedSonineProjectionFormula, burnolAmbientEvenPart,even] at formula
  have part : (1/2 : ℂ) • (value observation nontrivial half depth ordinal n+value observation nontrivial half depth ordinal n)=
      value observation nontrivial half depth ordinal n := by module
  rw [part] at formula
  exact formula

theorem actual_B_two_drives (ordinal n : Nat) :
    type_of% (burnolAmbientEvenMeanZeroCorrection_position (value observation nontrivial half depth ordinal n)) ∧
    type_of% (burnolAmbientEvenMeanZeroCorrection_fourier (value observation nontrivial half depth ordinal n)) :=
  ⟨burnolAmbientEvenMeanZeroCorrection_position _,burnolAmbientEvenMeanZeroCorrection_fourier _⟩

theorem actual_B_two_means (ordinal n : Nat) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (P (value observation nontrivial half depth ordinal n))) =
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (value observation nontrivial half depth ordinal n))-
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (burnolAmbientEvenMeanZeroCorrection (value observation nontrivial half depth ordinal n))) ∧
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (P (value observation nontrivial half depth ordinal n)))) =
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (value observation nontrivial half depth ordinal n)))-
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (burnolAmbientEvenMeanZeroCorrection (value observation nontrivial half depth ordinal n)))) := by
  rw [actual_B_projection]
  simp only [map_sub,burnolQuarterMeanCoefficient,inner_sub_right,sub_div,and_self]

theorem actual_K_covector (ordinal n : Nat) :
    inner ℂ (K c : BurnolL2) (P (value observation nontrivial half depth ordinal n)) =
      (Math.weight : ℂ)*inner ℂ (D (-Math.shift) (K c : BurnolL2)) (input observation nontrivial half depth ordinal).value -
      (Math.weight : ℂ)⁻¹*inner ℂ (D Math.shift (K c : BurnolL2)) (input observation nontrivial half depth ordinal).value := by
  have project : inner ℂ (K c : BurnolL2) (P (value observation nontrivial half depth ordinal n)) =
      inner ℂ (K c : BurnolL2) (value observation nontrivial half depth ordinal n) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K c) _
  rw [project,value_source]
  change inner ℂ (K c : BurnolL2) ((Math.weight : ℂ) • D Math.shift _-(Math.weight : ℂ)⁻¹ • D (-Math.shift) _) = _
  simp only [inner_sub_right,inner_smul_right,dilation_pair,neg_neg]

theorem actual_fixed_B_covector (ordinal n : Nat) :
    inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) (P (value observation nontrivial half depth ordinal n)) =
      (Math.weight : ℂ)*inner ℂ (D (-Math.shift) (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2)) (input observation nontrivial half depth ordinal).value -
      (Math.weight : ℂ)⁻¹*inner ℂ (D Math.shift (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2)) (input observation nontrivial half depth ordinal).value := by
  have project : inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) (P (value observation nontrivial half depth ordinal n)) =
      inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) (value observation nontrivial half depth ordinal n) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (BoundaryAdjointDefect.B.physicalCotest c) _
  rw [project,value_source]
  change inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) ((Math.weight : ℂ) • D Math.shift _-(Math.weight : ℂ)⁻¹ • D (-Math.shift) _) = _
  simp only [inner_sub_right,inner_smul_right,dilation_pair,neg_neg]

theorem actual_Gamma_covector (ordinal n : Nat) :
    inner ℂ (actualGammaKernel c) (P (value observation nontrivial half depth ordinal n)) =
      inner ℂ (sourceAnnulusCut (Math.action (OriginalGamma.Source.KappaConductor.originalDualLogValue c)))
        (PaNativePortSource.sourceMap ⟨Finite.pa (input observation nontrivial half depth ordinal).value,
          Finite.pa_mem _⟩) +
      inner ℂ (actualGammaKernel c) (Math.action (Finite.residual (input observation nontrivial half depth ordinal).value)) +
      inner ℂ (actualGammaKernel c) (Math.action (Finite.outside (input observation nontrivial half depth ordinal).value)) -
      inner ℂ (actualGammaKernel c) (burnolAmbientEvenMeanZeroCorrection (value observation nontrivial half depth ordinal n)) := by
  have source := congrArg (fun v : BurnolL2 => inner ℂ (actualGammaKernel c) (Math.action v))
    (Finite.split (input observation nontrivial half depth ordinal).value)
  rw [map_add,map_add,inner_add_right,inner_add_right] at source
  rw [Math.action_original, OriginalRSourceJointContact.ShiftedPaCovector.actual_primeThree_Gamma_Pa_source_price
    c observation.mathlibZero ⟨Finite.pa _,Finite.pa_mem _⟩] at source
  rw [actual_B_projection,inner_sub_right,value_source]
  exact congrArg (fun z : ℂ => z-inner ℂ (actualGammaKernel c)
    (burnolAmbientEvenMeanZeroCorrection (Math.action (input observation nontrivial half depth ordinal).value))) source.symm

theorem actual_physical_log_Gamma (ordinal n : Nat) :
    LogPair (P (value observation nontrivial half depth ordinal n))
      (CS.physical (fullSource observation nontrivial half depth ordinal)).position ∧
    GammaPair (P (value observation nontrivial half depth ordinal n))
      (CS.physical (fullSource observation nontrivial half depth ordinal)).gamma := by
  rw [←full_source_value observation nontrivial half depth ordinal n]
  exact ⟨(CS.physical (fullSource observation nontrivial half depth ordinal)).position_graph,
    (CS.physical (fullSource observation nontrivial half depth ordinal)).graph⟩

private theorem input_successor (ordinal : Nat) :
    burnolDirectRightResolventCLM c (input observation nontrivial half depth ordinal).value =
      (input observation nontrivial half depth (ordinal+1)).value := by
  have step (j : Nat) : burnolDirectRightResolventCLM c (raw j)=raw (j+1) :=
    (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half (raw j)).symm.trans
      (OriginalKCombFirstFullSourceDynamics.raw_successor observation nontrivial half depth j).symm
  change burnolDirectRightResolventCLM c (raw (ordinal+3)-raw (ordinal+1)) =
    raw (ordinal+1+3)-raw (ordinal+1+1)
  rw [map_sub]
  simpa only [Nat.add_assoc,Nat.reduceAdd] using
    congrArg₂ (fun left right : BurnolL2 => left-right) (step (ordinal+3)) (step (ordinal+1))

theorem actual_R_covariance (ordinal n : Nat) :
    burnolDirectRightResolventCLM c (value observation nontrivial half depth ordinal n) =
      Math.action (input observation nontrivial half depth (ordinal+1)).value :=
  (congrArg (burnolDirectRightResolventCLM c) (value_source observation nontrivial half depth ordinal n)).trans
    ((Math.action_resolvent c (input observation nontrivial half depth ordinal).value).symm.trans
      (congrArg Math.action (input_successor observation nontrivial half depth ordinal)))

/-- The actual source execution writes both physical branches before the independent reads. -/
theorem actual_prime_three_whole_R_source_writeback (ordinal n N : Nat) :
    type_of% (Install.input_from_original_receipt c n factory (nativeAt (ordinal+1))) ∧
    type_of% (Install.actual_equation c n factory (nativeAt (ordinal+1))) ∧
    type_of% (Install.actual_paid c n factory (nativeAt (ordinal+1))) ∧
    type_of% (value_source observation nontrivial half depth ordinal n) ∧
    type_of% (actual_strength observation nontrivial half depth ordinal n) ∧
    type_of% (actual_physical_live observation nontrivial half depth ordinal n) ∧
    type_of% (actual_joint_recovery observation nontrivial half depth ordinal n) ∧
    type_of% (actual_finite_source observation nontrivial half depth ordinal n N) ∧
    type_of% (actual_full_log_Gamma observation nontrivial half depth ordinal n) ∧
    type_of% (actual_B_projection observation nontrivial half depth ordinal n) ∧
    type_of% (actual_B_two_drives observation nontrivial half depth ordinal n) ∧
    type_of% (actual_B_two_means observation nontrivial half depth ordinal n) ∧
    type_of% (actual_fixed_B_covector observation nontrivial half depth ordinal n) ∧
    type_of% (actual_K_covector observation nontrivial half depth ordinal n) ∧
    type_of% (actual_Gamma_covector observation nontrivial half depth ordinal n) ∧
    type_of% (actual_physical_log_Gamma observation nontrivial half depth ordinal n) ∧
    type_of% (actual_R_covariance observation nontrivial half depth ordinal n) ∧
    type_of% (Install.source_trace c n factory (nativeAt (ordinal+1))) ∧
    type_of% (Install.born_inventory c n factory (nativeAt (ordinal+1))) ∧
    type_of% (Install.actual_receipt_next c n factory (nativeAt (ordinal+1))) ∧
    type_of% (Install.whole_first c n factory (nativeAt (ordinal+1))) ∧
    type_of% (Install.generated_next c n factory (nativeAt (ordinal+1))) :=
  ⟨Install.input_from_original_receipt c n factory (nativeAt (ordinal+1)),
   Install.actual_equation c n factory (nativeAt (ordinal+1)),
   Install.actual_paid c n factory (nativeAt (ordinal+1)),
   value_source observation nontrivial half depth ordinal n,
   actual_strength observation nontrivial half depth ordinal n,
   actual_physical_live observation nontrivial half depth ordinal n,
   actual_joint_recovery observation nontrivial half depth ordinal n,
   actual_finite_source observation nontrivial half depth ordinal n N,
   actual_full_log_Gamma observation nontrivial half depth ordinal n,
   actual_B_projection observation nontrivial half depth ordinal n,
   actual_B_two_drives observation nontrivial half depth ordinal n,
   actual_B_two_means observation nontrivial half depth ordinal n,
   actual_fixed_B_covector observation nontrivial half depth ordinal n,
   actual_K_covector observation nontrivial half depth ordinal n,
   actual_Gamma_covector observation nontrivial half depth ordinal n,
   actual_physical_log_Gamma observation nontrivial half depth ordinal n,
   actual_R_covariance observation nontrivial half depth ordinal n,
   Install.source_trace c n factory (nativeAt (ordinal+1)),
   Install.born_inventory c n factory (nativeAt (ordinal+1)),
   Install.actual_receipt_next c n factory (nativeAt (ordinal+1)),
   Install.whole_first c n factory (nativeAt (ordinal+1)),
   Install.generated_next c n factory (nativeAt (ordinal+1))⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
