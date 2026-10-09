import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCurvatureReaders
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalYResolvent
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullFieldRiesz
open GaussHistoryHilbert GaussCoreDifferential GaussDiagonalHistory GaussCoreHilbert GaussFockPair
open CanonicalPhysicalSpatial CanonicalGradedSpatialSource
open PreparationVacuumSourceActionJets PreparationVacuumFieldConstraintResponse PreparationVacuumSourcePreparedResponse
open PreparationVacuumSourcePreparedState
open GaussUnitaryHistory (Index sourceFilter)
open NativeHistoryGrade (Label projection)
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard PreparationScalarCoordinates GaussComposite GaussComposite.SourceGraph
open scoped Topology InnerProductSpace BigOperators
local instance : Fintype Label:=Fintype.ofFinite _

abbrev SourceSpan (F : GaussUnitaryHistory.Index) : Submodule ℂ GaussCoreHilbert.H := FiniteCoreEvolution.coreSpan GaussDiagonalHistory.diagonal F
abbrev BasisIndex (F : GaussUnitaryHistory.Index) := Fin (Module.finrank ℂ (SourceSpan F))
abbrev FrameIndex (F : GaussUnitaryHistory.Index) := Label × BasisIndex F

def sourceBasis (F : GaussUnitaryHistory.Index) : OrthonormalBasis (BasisIndex F) ℂ (SourceSpan F) := stdOrthonormalBasis ℂ (SourceSpan F)

def frameVector (F : GaussUnitaryHistory.Index) (i : FrameIndex F) : H := projection i.1 ((sourceBasis F i.2 : SourceSpan F) : H)

theorem frameVector_core (F : GaussUnitaryHistory.Index) (i : FrameIndex F) : frameVector F i∈Core :=
  GaussDiagonalGrade.stable i.1 ⟨(sourceBasis F i.2).val,FiniteCoreEvolution.coreSpan_le GaussDiagonalHistory.diagonal F (sourceBasis F i.2).property⟩

def frameTest (F : GaussUnitaryHistory.Index) (i : FrameIndex F) : QuantumTest := coreEquiv.symm ⟨frameVector F i,frameVector_core F i⟩

theorem frameTest_embed (F : GaussUnitaryHistory.Index) (i : FrameIndex F) : embed (frameTest F i)=frameVector F i :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply ⟨frameVector F i,frameVector_core F i⟩)

theorem sourceApprox_frame (F : GaussUnitaryHistory.Index) (x : H) :
    sourceApprox F x=∑ i : FrameIndex F,inner ℂ (frameVector F i) x • frameVector F i := by
  rw [sourceApprox_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro label _
  rw [(sourceBasis F).starProjection_eq_sum_rankOne]
  simp only [sum_apply,InnerProductSpace.rankOne_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun c : ℂ=>c • frameVector F (label,j))
    (NativeHistoryGrade.projection_symmetric label ((sourceBasis F j : SourceSpan F) : H) x).symm

theorem sourceTestApprox_frame (F : GaussUnitaryHistory.Index) (x : H) :
    sourceTestApprox F x=∑ i : FrameIndex F,inner ℂ (frameVector F i) x • frameTest F i := by
  apply embed_injective
  rw [sourceTestApprox_embed,map_sum]
  simp only [map_smul,frameTest_embed]
  exact sourceApprox_frame F x

def finiteRiesz (F : GaussUnitaryHistory.Index) (entries : FrameIndex F → FrameIndex F → ℂ) : H →L[ℂ] H :=
  ∑ i : FrameIndex F,∑ j : FrameIndex F,entries i j • InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j)

def finitePrice (F : GaussUnitaryHistory.Index) (entries : FrameIndex F → FrameIndex F → ℂ) : ℝ :=
  ∑ i : FrameIndex F,∑ j : FrameIndex F,‖entries i j‖*‖frameVector F i‖*‖frameVector F j‖

theorem finitePrice_nonnegative (F : GaussUnitaryHistory.Index) (entries : FrameIndex F → FrameIndex F → ℂ) : 0≤finitePrice F entries := by
  unfold finitePrice
  exact Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>by positivity))

theorem finiteRiesz_price (F : GaussUnitaryHistory.Index) (entries : FrameIndex F → FrameIndex F → ℂ) : ‖finiteRiesz F entries‖≤finitePrice F entries := by
  unfold finiteRiesz finitePrice
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul,InnerProductSpace.norm_rankOne]
  exact le_of_eq (mul_assoc _ _ _).symm

theorem finiteRiesz_pair (F : GaussUnitaryHistory.Index) (entries : FrameIndex F → FrameIndex F → ℂ) (x y : H) :
    inner ℂ x (finiteRiesz F entries y)=
      ∑ i : FrameIndex F,∑ j : FrameIndex F,
        star (inner ℂ (frameVector F i) x)*entries i j*inner ℂ (frameVector F j) y := by
  simp only [finiteRiesz,sum_apply,smul_apply,InnerProductSpace.rankOne_apply,inner_sum,inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [←inner_conj_symm x (frameVector F i)]
  simp only [starRingEnd_apply]
  ring

-- The finite price and frame come from the original F, not a supplied Riesz
-- realization or a replacement physical compression.
def fieldMatrix (f : PreparationVacuumMixedFieldReturn.Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (r : ℝ) :
    FrameIndex F → FrameIndex F → ℂ := fun i j=>fieldForm f p (frameTest F i) (frameTest F j) r

def formRestriction (f : PreparationVacuumMixedFieldReturn.Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (r : ℝ) : H →L[ℂ] H :=
  finiteRiesz F (fieldMatrix f p F r)

def currentRestriction (f : PreparationVacuumMixedFieldReturn.Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (r : ℝ) : H →L[ℂ] H :=
  finiteRiesz F (fun i j=>(fieldJets f p (frameTest F i) (frameTest F j)).first r)

def contactRestriction (f : PreparationVacuumMixedFieldReturn.Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H →L[ℂ] H :=
  finiteRiesz F (fun i j=>(fieldJets f p (frameTest F i) (frameTest F j)).second)

theorem formRestriction_first (f : PreparationVacuumMixedFieldReturn.Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (formRestriction f p F) (currentRestriction f p F 0) 0 := by
  unfold formRestriction currentRestriction finiteRiesz fieldMatrix
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact ((fieldJets f p (frameTest F i) (frameTest F j)).actual.1).smul_const (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))

theorem currentRestriction_second (f : PreparationVacuumMixedFieldReturn.Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (currentRestriction f p F) (contactRestriction f p F) 0 := by
  unfold currentRestriction contactRestriction finiteRiesz
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact ((fieldJets f p (frameTest F i) (frameTest F j)).second_derivative).smul_const (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))

theorem formRestriction_original_pair (f : PreparationVacuumMixedFieldReturn.Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (formRestriction f p F 0 y)=sourcePair (sourceTestApprox F x)
      ((CanonicalPhysicalSpatial.physicalAction p+GaussYukawaOperator.originalAction) (sourceTestApprox F y)) := by
  rw [formRestriction,finiteRiesz_pair,sourceTestApprox_frame,sourceTestApprox_frame]
  simp only [fieldMatrix,fieldForm_source,sourcePair,map_sum,map_smul,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,Finset.mul_sum]
  conv_rhs=>rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [starRingEnd_apply]
  ring

theorem actual_prepared_frame (epsilon : ℝ) (precision : 0<epsilon) (F : GaussUnitaryHistory.Index) (addition : Bool) (a s : Fin 2) :
    sourceTestApprox F (completedLeg addition a s (sourceProfile epsilon precision))=
      ∑ i : FrameIndex F,inner ℂ (frameVector F i) (completedLeg addition a s (sourceProfile epsilon precision)) • frameTest F i :=
  sourceTestApprox_frame F _

end LowEnergy.PreparationVacuumFullFieldRiesz
