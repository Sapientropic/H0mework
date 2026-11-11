import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestEuler

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRReciprocalCotestActionSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource OriginalRieszFiniteColumns
open OriginalKSourceResolventReconstruction
open OriginalWholeDebtRPowerWaveDilationSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "h" => OriginalKPairedBEulerJunctionSource.junctionShift
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "DT" => TemperedDistribution ℝ ℂ
local notation "F" => fourierL2
local notation "U" => burnolMultiplicativeDilation
local notation "Tate" => burnolTateReciprocalL2
local notation "Eq" => burnolQuarterZeroExtension
local notation "cut" => OriginalPaPhysicalGreen.originalPhysicalCutoff
local notation "step" => OriginalWholeDebtRAdjointContactSource.step
open private step_euler from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
open private actual_R_euler from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestSource

private theorem forward_contact_euler (c : BurnolCompletedMellinCoordinate) (radius : ℝ)
    (positive : 0<radius) :
    GapEuler.euler (forwardContact c radius : DT)+
      frequency c • (forwardContact c radius : DT)=
        (-(2 : ℂ)*(radius : ℂ)) •
          (TemperedDistribution.delta radius+TemperedDistribution.delta (-radius)) := by
  have acted := actual_R_euler c (step radius)
  have edge := step_euler radius positive
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (forwardContact c radius))+
    frequency c • Lp.toTemperedDistributionCLM ℂ volume 2 (forwardContact c radius)=_
  simp only [forwardContact,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
  unfold frequency at acted ⊢
  linear_combination (norm := module) c.value • acted+(2 : ℂ) • edge

/-- The full reciprocal source forcing and both actual contacts determine Rr. -/
theorem weighted_field_action (c : BurnolCompletedMellinCoordinate) :
    weightedField c=weight c • burnolDirectRightResolventCLM c (reciprocalCotest c) := by
  have native:=actual_reciprocal_euler c
  have acted:=actual_R_euler c (forcing c)
  have lowerContact:=forward_contact_euler c lower (by unfold lower;positivity)
  have upperContact:=forward_contact_euler c 4 (by norm_num)
  have original:=actual_R_euler c (reciprocalCotest c)
  let difference:=weightedField c-weight c •
    burnolDirectRightResolventCLM c (reciprocalCotest c)
  have homogeneous : GapEuler.euler (difference : DT)+frequency c • (difference : DT)=0 := by
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 difference)+
      frequency c • Lp.toTemperedDistributionCLM ℂ volume 2 difference=0
    simp only [difference,weightedField,map_sub,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
    unfold weight at ⊢
    unfold frequency at native acted lowerContact upperContact original ⊢
    linear_combination (norm := module)
      acted-lowerTrace c • lowerContact+upperTrace c • upperContact-
        (2 : ℂ) • native-(2*c.value-1) • original
  have zero:=homogeneous_L2_unique (frequency c)
    (by simp only [frequency,Complex.sub_re];norm_num;linarith [c.rightHalf]) difference homogeneous
  exact sub_eq_zero.mp zero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "coordinate" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
namespace Flux
export FiniteMobiusResolventFlux
  (D sourceDefect defectForcing sourceA Rplus original_defect_source_readback)
namespace Prior
export FiniteMobiusResolventFlux.Prior (originalK)
end Prior
end Flux

private theorem fourier_defect_source :
    Flux.D (F (generatedK coordinate))=
      -Tate (Flux.sourceDefect observation nontrivial half) := by
  have kernel : generatedK coordinate=Flux.Prior.originalK observation nontrivial half := by
    rw [generatedK_eq_original]
    rfl
  have even : reflectL2 (generatedK coordinate)=generatedK coordinate := by
    rw [generatedK_eq_original]
    exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector coordinate).property.2
  have actual := Flux.original_defect_source_readback observation nontrivial half
  rw [←kernel] at actual
  rw [←actual]
  unfold Flux.D
  simp only [sub_apply,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry,
    fourierL2_fourierL2,even,map_sub,burnolTateReciprocalL2_involutive]
  module

/-- The original full defect fee now consumes the generated forcing/contact R field. -/
theorem actual_defect_fee :
    star (weight coordinate)*inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate) 0)
      (Flux.D (F (generatedK coordinate)))=
      inner ℂ (effectCotest coordinate) (Flux.defectForcing observation nontrivial half) := by
  let originalForcing:=Flux.defectForcing observation nontrivial half
  have literal := OriginalKCombCofinalTwoDirection.coordinate_value observation nontrivial half
  have right : 1/4<((coordinate).value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [(coordinate).rightHalf]
  have adjoint:=OriginalKCompactAdjointRSource.actual_original_R_adjoint
    ((coordinate).value/2) right originalForcing (reciprocalCotest coordinate)
  have dual : inner ℂ (reciprocalCotest coordinate)
      (Flux.Rplus (star observation.coordinate/2) originalForcing)=
        inner ℂ (burnolDirectRightResolventCLM coordinate (reciprocalCotest coordinate)) originalForcing := by
    change inner ℂ (reciprocalCotest coordinate)
      (Flux.Rplus (star observation.coordinate/2) originalForcing)=
        inner ℂ (burnolDirectRightResolvent ((coordinate).value/2) (reciprocalCotest coordinate)) originalForcing
    have reflected:=congrArg (starRingEnd ℂ) adjoint
    simpa only [inner_conj_symm,star_div₀,star_ofNat,literal] using reflected.symm
  have fee : inner ℂ (burnolAnnulusSamplingL2 (fourierColumn coordinate) 0)
      (Flux.D (F (generatedK coordinate)))=
        inner ℂ (reciprocalCotest coordinate) originalForcing+
          sourceA coordinate*inner ℂ
            (burnolDirectRightResolventCLM coordinate (reciprocalCotest coordinate)) originalForcing := by
    rw [fourier_defect_source,inner_neg_right,
      ←OriginalRieszFiniteSynthesis.tate_pairing,Flux.sourceDefect,
      inner_sub_right,inner_neg_right,inner_smul_right]
    change -( -inner ℂ (reciprocalCotest coordinate) originalForcing-
      Flux.sourceA observation*inner ℂ (reciprocalCotest coordinate)
        (Flux.Rplus (star observation.coordinate/2) originalForcing))=_
    rw [dual]
    simp only [Flux.sourceA,sourceA,literal]
    ring
  change _=inner ℂ (effectCotest coordinate) originalForcing
  rw [fee]
  simp only [effectCotest,weighted_field_action,inner_add_left,inner_smul_left,
    starRingEnd_apply,star_star]
  ring
end OriginalWholeDebtRReciprocalCotestActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
