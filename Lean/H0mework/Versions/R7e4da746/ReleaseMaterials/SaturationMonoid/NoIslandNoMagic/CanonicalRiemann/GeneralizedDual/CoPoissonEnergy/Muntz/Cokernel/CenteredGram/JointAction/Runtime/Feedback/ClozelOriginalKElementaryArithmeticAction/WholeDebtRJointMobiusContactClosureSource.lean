import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.BPowerCayleySource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusContactClosureSource
open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKSourceResolventReconstruction
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open OriginalWholeDebtRAdjointContactSource
open scoped InnerProductSpace
open private full_source_balance from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource
open private correction_outside power_fourier_quarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private quarter_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Action
open private source_C_adjoint_block from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private actualAdjoint_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source
local notation "F" => fourierL2
local notation "P" => burnolEvenAmbientProjectionEndomorphism
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "C" => correctionRaw
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Eq" => burnolQuarterZeroExtension

/-- The complete B solve supplies this finite quarter pairing, including the actual second source mean. -/
def finitePrice (c d : BurnolCompletedMellinCoordinate) : ℂ :=
  inner ℂ (SingularCounting.centeredPower (barC d)) (sourceSecond c)

def coefficient (c d : BurnolCompletedMellinCoordinate) : ℂ := -2*sigma c d*finitePrice c d

/-- All regular and signed contact terms are executed before physical projection. -/
def closureInput (c d : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection (sourceEffect c d)

def next (c d : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolDirectRightResolventCLM d (closureInput c d)

/-- Both complete B columns are consumed; the first vanishes by its actual Fourier-quarter source law. -/
theorem actual_finite_price (c d : BurnolCompletedMellinCoordinate) :
    inner ℂ (physicalOutsideColumn d) (C c)=finitePrice c d := by
  have secondEven : reflectL2 (Eq (sourceSecond c : Hq))=Eq (sourceSecond c : Hq) := by
    change reflectL2 (burnolRadiusZeroExtension (1/4) (sourceSecond c : Hq))=_
    rw [burnolRadiusZeroExtension_reflect]
    change burnolRadiusZeroExtension (1/4) (reflectRestricted (1/4) (sourceCorrection c 1 : Hq))=_
    rw [source_correction_even c 1]
    rfl
  have transported:=fourierL2.inner_map_map (physicalOutsideColumn d) (F (Eq (sourceSecond c : Hq)))
  change inner ℂ (F (fourierL2.symm (hPowerPhysicalCorrection (barC d))))
    (F (F (Eq (sourceSecond c : Hq))))=_ at transported
  rw [fourierL2.apply_symm_apply,fourierL2_fourierL2,secondEven] at transported
  unfold correctionRaw
  rw [inner_add_right,quarter_pair]
  change inner ℂ (quarterCotest (fourierL2.symm (hPowerPhysicalCorrection (barC d)))) (sourceFirst c)+_= _
  rw [power_fourier_quarter,inner_zero_left,zero_add,←transported,quarter_pair,powerCorrection_quarter_source]
  rfl

private theorem correction_physical_zero (c : BurnolCompletedMellinCoordinate) : P (C c)=0 := by
  have whole : O (C c)=C c-P (C c) := Submodule.starProjection_orthogonal_val _
  rw [correction_outside] at whole
  linear_combination (norm:=module) whole

private theorem adjoint_physical_block (c d : BurnolCompletedMellinCoordinate) :
    P (T d (C c))=(-2*finitePrice c d) • F (generatedK d) := by
  have block:=source_C_adjoint_block d (C c)
  rw [correction_outside,sourceCayley_actual_adjoint,sourceAdjointCayley,map_add,map_smul,
    correction_physical_zero,zero_add,actual_finite_price] at block
  have dampingNe : (sourceDamping d : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sourceDamping_pos d))
  have scaled:=congrArg (fun v : BurnolL2=>(sourceDamping d : ℂ)⁻¹ • v) block
  rw [smul_smul,inv_mul_cancel₀ dampingNe,one_smul,smul_smul] at scaled
  have scalar : (sourceDamping d : ℂ)⁻¹*(-2*(sourceDamping d : ℂ)*finitePrice c d)= -2*finitePrice c d := by
    field_simp [dampingNe]
  rw [scalar,←actualAdjoint_read] at scaled
  exact scaled

/-- The source, not a supplied FK target, generates the literal physical input. -/
theorem actual_input (c d : BurnolCompletedMellinCoordinate) :
    (closureInput c d : BurnolL2)=coefficient c d • F (generatedK d) := by
  have whole:=congrArg P (full_source_balance c d)
  rw [map_add,map_smul,map_smul,correction_physical_zero,smul_zero,add_zero,
    adjoint_physical_block,smul_smul] at whole
  change P (sourceEffect c d)=_
  rw [whole]
  congr 1
  unfold coefficient
  ring

/-- The existing full original R consumes the generated physical source input. -/
theorem actual_next (c d : BurnolCompletedMellinCoordinate) :
    next c d=coefficient c d • sourceFKAction d := by
  unfold next
  rw [actual_input,map_smul]
  exact congrArg (fun v : BurnolL2=>coefficient c d • v) (original_R_FK_generated d)

/-- Its K, FK and complete B column remain one whole native update. -/
theorem actual_whole_next (c d : BurnolCompletedMellinCoordinate) :
    next c d=coefficient c d •
      ((sourceForwardRatio d/(sourceDamping d : ℂ)) • generatedK (barC d)-
        (sourceDamping d : ℂ)⁻¹ • F (generatedK d)-
        (2*((‖generatedK d‖^2 : ℝ) : ℂ)) • physicalOutsideColumn d) :=
  actual_next c d

/-- Independent original physical-R action reads the same whole source's B price. -/
theorem actual_B_effect (c d : BurnolCompletedMellinCoordinate) :
    O (next c d)=(-2*inner ℂ (F (generatedK d)) (closureInput c d : BurnolL2)) • physicalOutsideColumn d :=
  original_R_physical_outside_source d (closureInput c d)

end OriginalWholeDebtRJointMobiusContactClosureSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
