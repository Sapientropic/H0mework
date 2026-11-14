import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.RNext.Install

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Consumer
open BurnolPhysicalState OriginalGamma.Source.FiniteLogCounting OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.KGamma
open scoped InnerProductSpace
namespace Previous
export OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer
  (value value_source fullSource full_source_value actual_R_covariance actual_physical_live)
end Previous
namespace I
export Install (value value_source)
end I
namespace CS
export BoundaryNativeKConductorSource (Source physical)
end CS
attribute [local irreducible] Install.frame Install.grade
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ j : Nat, observation.coordinate=-2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth n : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

theorem actual_R_value (ordinal : Nat) : I.value observation nontrivial half depth n ordinal=
    R c (Previous.value observation nontrivial half depth ordinal n) :=
  (I.value_source observation nontrivial half depth n ordinal).trans
    ((congrArg (OriginalKCombPhysicalAction.R observation nontrivial half)
      (Install.current_value observation nontrivial half depth n ordinal)).trans
        (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half _))

def fullSource (ordinal : Nat) : CS.Source :=
  Material.resolve c (Previous.fullSource observation nontrivial half depth ordinal)

theorem full_source_value (ordinal : Nat) : (fullSource observation nontrivial half depth ordinal).value=
    I.value observation nontrivial half depth n ordinal :=
  (Material.resolve_value c (Previous.fullSource observation nontrivial half depth ordinal)).trans
    ((congrArg (R c) (Previous.full_source_value observation nontrivial half depth ordinal n)).trans
      (actual_R_value observation nontrivial half depth n ordinal).symm)

theorem actual_log_Gamma (ordinal : Nat) :
    LogPair (I.value observation nontrivial half depth n ordinal) (fullSource observation nontrivial half depth ordinal).position ∧
    LogPair (fourierL2.symm (I.value observation nontrivial half depth n ordinal)) (fullSource observation nontrivial half depth ordinal).inverse ∧
    GammaPair (I.value observation nontrivial half depth n ordinal) (fullSource observation nontrivial half depth ordinal).gamma ∧
    (fullSource observation nontrivial half depth ordinal).gamma=R c (Previous.fullSource observation nontrivial half depth ordinal).gamma := by
  rw [←full_source_value observation nontrivial half depth n ordinal]
  exact ⟨(fullSource observation nontrivial half depth ordinal).position_graph,
    (fullSource observation nontrivial half depth ordinal).inverse_graph,
    (fullSource observation nontrivial half depth ordinal).graph,Material.resolve_gamma c _⟩

theorem actual_rho_successor (ordinal : Nat) :
    I.value observation nontrivial half depth n ordinal=
      Math.action (OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer.input
        observation nontrivial half depth (ordinal+1)).value :=
  (actual_R_value observation nontrivial half depth n ordinal).trans
    (Previous.actual_R_covariance observation nontrivial half depth ordinal n)

theorem actual_physical_live (ordinal : Nat) : P (I.value observation nontrivial half depth n ordinal) ≠ 0 := by
  have same : I.value observation nontrivial half depth n ordinal=Previous.value observation nontrivial half depth (ordinal+1) n :=
    (actual_rho_successor observation nontrivial half depth n ordinal).trans
      (Previous.value_source observation nontrivial half depth (ordinal+1) n).symm
  rw [same]
  exact Previous.actual_physical_live observation nontrivial half depth (ordinal+1) n

theorem actual_joint_recovery (ordinal : Nat) :
    Program.Inverse.operator (P (I.value observation nontrivial half depth n ordinal)+O (I.value observation nontrivial half depth n ordinal))=
      (OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer.input
        observation nontrivial half depth (ordinal+1)).value := by
  rw [OriginalKCombFullResidualAction.split_complete,actual_rho_successor]
  exact Program.Inverse.recover _

theorem actual_B_projection (ordinal : Nat) : P (I.value observation nontrivial half depth n ordinal)=
    I.value observation nontrivial half depth n ordinal-burnolAmbientEvenMeanZeroCorrection (I.value observation nontrivial half depth n ordinal) := by
  have formula := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula (I.value observation nontrivial half depth n ordinal)
  change P (I.value observation nontrivial half depth n ordinal)=_ at formula
  have even := (fullSource observation nontrivial half depth ordinal).even
  rw [full_source_value observation nontrivial half depth n ordinal] at even
  rw [burnolAmbientExtendedSonineProjectionFormula,burnolAmbientEvenPart,even] at formula
  have part : (1/2 : ℂ) • (I.value observation nontrivial half depth n ordinal+I.value observation nontrivial half depth n ordinal)=
      I.value observation nontrivial half depth n ordinal := by module
  rw [part] at formula
  exact formula

theorem actual_B_two_means (ordinal : Nat) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (P (I.value observation nontrivial half depth n ordinal)))=
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (I.value observation nontrivial half depth n ordinal))-
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (burnolAmbientEvenMeanZeroCorrection (I.value observation nontrivial half depth n ordinal))) ∧
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (P (I.value observation nontrivial half depth n ordinal))))=
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (I.value observation nontrivial half depth n ordinal)))-
      burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (burnolAmbientEvenMeanZeroCorrection (I.value observation nontrivial half depth n ordinal)))) := by
  rw [actual_B_projection]
  simp only [map_sub,burnolQuarterMeanCoefficient,inner_sub_right,sub_div,and_self]

theorem actual_K_covector (ordinal : Nat) :
    inner ℂ (K c : BurnolL2) (P (I.value observation nontrivial half depth n ordinal))=
      inner ℂ ((R c).adjoint (K c : BurnolL2)) (Previous.value observation nontrivial half depth ordinal n) := by
  have projected : inner ℂ (K c : BurnolL2) (P (I.value observation nontrivial half depth n ordinal))=
      inner ℂ (K c : BurnolL2) (I.value observation nontrivial half depth n ordinal) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K c) _
  exact projected.trans ((congrArg (inner ℂ (K c : BurnolL2)) (actual_R_value observation nontrivial half depth n ordinal)).trans
    (ContinuousLinearMap.adjoint_inner_left (R c) _ (K c : BurnolL2)).symm)

theorem actual_fixed_B_covector (ordinal : Nat) :
    inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) (P (I.value observation nontrivial half depth n ordinal))=
      inner ℂ ((R c).adjoint (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2))
        (Previous.value observation nontrivial half depth ordinal n) := by
  have projected : inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) (P (I.value observation nontrivial half depth n ordinal))=
      inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) (I.value observation nontrivial half depth n ordinal) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (BoundaryAdjointDefect.B.physicalCotest c) _
  exact projected.trans ((congrArg (inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2))
    (actual_R_value observation nontrivial half depth n ordinal)).trans
    (ContinuousLinearMap.adjoint_inner_left (R c) _ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2)).symm)

theorem actual_Gamma_covector (ordinal : Nat) :
    inner ℂ (actualGammaKernel c) (P (I.value observation nontrivial half depth n ordinal))=
      inner ℂ ((R c).adjoint (actualGammaKernel c)) (Previous.value observation nontrivial half depth ordinal n)-
      inner ℂ (actualGammaKernel c) (burnolAmbientEvenMeanZeroCorrection (I.value observation nontrivial half depth n ordinal)) := by
  rw [actual_B_projection,inner_sub_right,actual_R_value]
  exact congrArg (fun z : ℂ => z-inner ℂ (actualGammaKernel c)
    (burnolAmbientEvenMeanZeroCorrection (R c (Previous.value observation nontrivial half depth ordinal n))))
    (ContinuousLinearMap.adjoint_inner_left (R c) _ (actualGammaKernel c)).symm

theorem actual_physical_logs (ordinal : Nat) :
    LogPair (P (I.value observation nontrivial half depth n ordinal)) (CS.physical (fullSource observation nontrivial half depth ordinal)).position ∧
    LogPair (fourierL2.symm (P (I.value observation nontrivial half depth n ordinal)))
      (CS.physical (fullSource observation nontrivial half depth ordinal)).inverse ∧
    GammaPair (P (I.value observation nontrivial half depth n ordinal)) (CS.physical (fullSource observation nontrivial half depth ordinal)).gamma := by
  rw [←full_source_value observation nontrivial half depth n ordinal]
  exact ⟨(CS.physical (fullSource observation nontrivial half depth ordinal)).position_graph,
    (CS.physical (fullSource observation nontrivial half depth ordinal)).inverse_graph,
    (CS.physical (fullSource observation nontrivial half depth ordinal)).graph⟩

/-- The original R reader consumes the generated current stock and pays its actual successor. -/
theorem actual_prime_three_R_next_writeback (ordinal : Nat) :
    type_of% (Install.seed_source observation nontrivial half depth n ordinal) ∧
    type_of% (Install.frame_generated observation nontrivial half depth n ordinal) ∧
    type_of% (Install.current_value observation nontrivial half depth n ordinal) ∧
    type_of% (Install.actual_occurrence observation nontrivial half depth n ordinal) ∧
    type_of% (Install.actual_reader observation nontrivial half depth n ordinal) ∧
    type_of% (Install.actual_environment observation nontrivial half depth n ordinal) ∧
    type_of% (Install.actual_equation observation nontrivial half depth n ordinal) ∧
    type_of% (Install.material_raw observation nontrivial half depth n ordinal) ∧
    type_of% (Install.actual_paid observation nontrivial half depth n ordinal) ∧
    type_of% (@Install.actual_born_write observation nontrivial half depth n ordinal) ∧
    type_of% (actual_R_value observation nontrivial half depth n ordinal) ∧
    type_of% (actual_log_Gamma observation nontrivial half depth n ordinal) ∧
    type_of% (actual_rho_successor observation nontrivial half depth n ordinal) ∧
    type_of% (actual_physical_live observation nontrivial half depth n ordinal) ∧
    type_of% (actual_joint_recovery observation nontrivial half depth n ordinal) ∧
    type_of% (actual_B_two_means observation nontrivial half depth n ordinal) ∧
    type_of% (actual_K_covector observation nontrivial half depth n ordinal) ∧
    type_of% (actual_fixed_B_covector observation nontrivial half depth n ordinal) ∧
    type_of% (actual_Gamma_covector observation nontrivial half depth n ordinal) ∧
    type_of% (actual_physical_logs observation nontrivial half depth n ordinal) ∧
    type_of% (Install.actual_compiles observation nontrivial half depth n ordinal) ∧
    type_of% (Install.source_trace observation nontrivial half depth n ordinal) ∧
    type_of% (Install.born_inventory observation nontrivial half depth n ordinal) ∧
    type_of% (Install.actual_receipt_next observation nontrivial half depth n ordinal) ∧
    type_of% (Install.whole_first observation nontrivial half depth n ordinal) ∧
    type_of% (Install.old_outcome observation nontrivial half depth n ordinal) ∧
    type_of% (Install.generated_next observation nontrivial half depth n ordinal) :=
  ⟨Install.seed_source observation nontrivial half depth n ordinal,
   Install.frame_generated observation nontrivial half depth n ordinal,
   Install.current_value observation nontrivial half depth n ordinal,
   Install.actual_occurrence observation nontrivial half depth n ordinal,
   Install.actual_reader observation nontrivial half depth n ordinal,
   Install.actual_environment observation nontrivial half depth n ordinal,
   Install.actual_equation observation nontrivial half depth n ordinal,
   Install.material_raw observation nontrivial half depth n ordinal,
   Install.actual_paid observation nontrivial half depth n ordinal,
   @Install.actual_born_write observation nontrivial half depth n ordinal,
   actual_R_value observation nontrivial half depth n ordinal,
   actual_log_Gamma observation nontrivial half depth n ordinal,
   actual_rho_successor observation nontrivial half depth n ordinal,
   actual_physical_live observation nontrivial half depth n ordinal,
   actual_joint_recovery observation nontrivial half depth n ordinal,
   actual_B_two_means observation nontrivial half depth n ordinal,
   actual_K_covector observation nontrivial half depth n ordinal,
   actual_fixed_B_covector observation nontrivial half depth n ordinal,
   actual_Gamma_covector observation nontrivial half depth n ordinal,
   actual_physical_logs observation nontrivial half depth n ordinal,
   Install.actual_compiles observation nontrivial half depth n ordinal,
   Install.source_trace observation nontrivial half depth n ordinal,
   Install.born_inventory observation nontrivial half depth n ordinal,
   Install.actual_receipt_next observation nontrivial half depth n ordinal,
   Install.whole_first observation nontrivial half depth n ordinal,
   Install.old_outcome observation nontrivial half depth n ordinal,
   Install.generated_next observation nontrivial half depth n ordinal⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
