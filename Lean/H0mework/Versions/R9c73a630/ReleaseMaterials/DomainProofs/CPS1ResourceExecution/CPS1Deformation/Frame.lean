import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Fields
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource ContinuousLinearMap
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

abbrev CoefficientSpace (state : CPS1ElectronicSource.State frame) :=
  EuclideanSpace ℂ (CPS1MolecularFrame.ActualIndex state)

def frameAt (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state) :
    CoefficientSpace state →L[ℂ] SpinSpace := CPS1MolecularFrame.fieldFrame (basisAt state positions)

def fieldEmbedding (state : CPS1ElectronicSource.State frame) (index : CPS1MolecularFrame.ActualIndex state) :
    SpinSpace →L[ℝ] (CoefficientSpace state →L[ℂ] SpinSpace) :=
  (ContinuousLinearMap.smulRightL ℂ (CoefficientSpace state) SpinSpace
    (PiLp.proj 2 (fun _ : CPS1MolecularFrame.ActualIndex state => ℂ) index)).restrictScalars ℝ

def frameFDeriv (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state) :
    NuclearConfiguration state →L[ℝ] (CoefficientSpace state →L[ℂ] SpinSpace) :=
  ∑ index, (fieldEmbedding state index).comp (basisFDeriv state positions index)

theorem field_embedding_apply (state : CPS1ElectronicSource.State frame)
    (index : CPS1MolecularFrame.ActualIndex state) (field : SpinSpace) (coefficient : CoefficientSpace state) :
    fieldEmbedding state index field coefficient = coefficient index • field := rfl

theorem frame_hasFDerivAt (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state) :
    HasFDerivAt (frameAt state) (frameFDeriv state positions) positions := by
  have source := HasFDerivAt.fun_sum (u := Finset.univ) (fun index _ =>
    (fieldEmbedding state index).hasFDerivAt.comp positions (basis_hasFDerivAt state positions index))
  exact source

theorem frame_fderiv_apply (state : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration state) :
    frameFDeriv state positions direction =
      CPS1MolecularFrame.fieldFrame (fun index => basisFDeriv state positions index direction) := by
  ext1 coefficient
  simp only [frameFDeriv,sum_apply,comp_apply,field_embedding_apply,CPS1MolecularFrame.field_frame_apply]

def gramAt (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state) :
    CoefficientSpace state →L[ℂ] CoefficientSpace state := LAlanineSpatialProjection.gram (frameAt state positions)

def gramFDeriv (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state) :
    NuclearConfiguration state →L[ℝ] (CoefficientSpace state →L[ℂ] CoefficientSpace state) :=
  ((compL ℂ (CoefficientSpace state) SpinSpace (CoefficientSpace state)).bilinearRestrictScalars ℝ).precompR
      (NuclearConfiguration state) (frameAt state positions).adjoint (frameFDeriv state positions) +
    ((compL ℂ (CoefficientSpace state) SpinSpace (CoefficientSpace state)).bilinearRestrictScalars ℝ).precompL
      (NuclearConfiguration state) (LAlanineSpatialProjection.adjointReal.comp (frameFDeriv state positions))
      (frameAt state positions)

theorem gram_hasFDerivAt (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state) :
    HasFDerivAt (gramAt state) (gramFDeriv state positions) positions := by
  have source := frame_hasFDerivAt state positions
  have adjoint := LAlanineSpatialProjection.adjointReal.hasFDerivAt.comp positions source
  exact ((compL ℂ (CoefficientSpace state) SpinSpace (CoefficientSpace state)).bilinearRestrictScalars ℝ).hasFDerivAt_of_bilinear adjoint source

theorem gram_fderiv_apply (state : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration state) :
    gramFDeriv state positions direction =
      LAlanineSpatialProjection.gramRate (frameAt state positions) (frameFDeriv state positions direction) := by
  simp only [gramFDeriv,add_apply,precompR_apply,precompL_apply,bilinearRestrictScalars_apply_apply,
    compL_apply,comp_apply,LAlanineSpatialProjection.adjointReal,LAlanineSpatialProjection.gramRate]
  exact add_comm _ _

theorem source_line_initial (state : CPS1ElectronicSource.State frame) :
    sourceLine state 0 = sourcePositions state := by
  funext nuclear
  exact CPS1MolecularFrame.centre_line_initial state nuclear

theorem frame_source (state : CPS1ElectronicSource.State frame) :
    frameAt state (sourcePositions state) = CPS1MolecularFrame.frameCurve state 0 := by
  rw [frameAt,basis_source,CPS1MolecularFrame.frame_curve_initial]

theorem frame_line (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    frameAt state (sourceLine state time) = CPS1MolecularFrame.frameCurve state time := by
  rw [frameAt,basis_line]
  rfl

theorem frame_rate_source (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    frameFDeriv state (sourceLine state time) (sourceVelocity state) = CPS1MolecularFrame.frameRate state time := by
  rw [frame_fderiv_apply]
  simp only [basis_rate_source]
  rfl

theorem gram_source_one (state : CPS1ElectronicSource.State frame) : gramAt state (sourcePositions state) = 1 := by
  rw [gramAt,frameAt,basis_source,CPS1MolecularFrame.field_frame_gram]
  have normalized : Matrix.gram ℂ (CPS1MolecularFrame.currentBasis state) = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr
    (CPS1MolecularFrame.FiniteNormed.field_orthonormal (𝕜 := ℂ) (CPS1MolecularFrame.rawField state))
  rw [normalized,map_one]

theorem source_gram_unit (state : CPS1ElectronicSource.State frame) :
    IsUnit (LAlanineSpatialProjection.gram (frameAt state (sourcePositions state))) := by
  rw [← gramAt,gram_source_one]
  exact isUnit_one

def projectionAt (state : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration state) :
    SpinSpace →L[ℂ] SpinSpace := LAlanineSpatialProjection.totalProjection (frameAt state positions)

def projectionFDeriv (state : CPS1ElectronicSource.State frame) :
    NuclearConfiguration state →L[ℝ] (SpinSpace →L[ℂ] SpinSpace) :=
  fderiv ℝ (projectionAt state) (sourcePositions state)

theorem projection_hasFDerivAt (state : CPS1ElectronicSource.State frame) :
    HasFDerivAt (projectionAt state) (projectionFDeriv state) (sourcePositions state) := by
  let positions := sourcePositions state
  have mother := frame_hasFDerivAt state positions
  have gram := gram_hasFDerivAt state positions
  have inverse := hasFDerivAt_ringInverse (𝕜 := ℝ) (source_gram_unit state).unit
  rw [(source_gram_unit state).unit_spec] at inverse
  have inverseField := inverse.comp positions gram
  have first := ((compL ℂ (CoefficientSpace state) (CoefficientSpace state) SpinSpace).bilinearRestrictScalars ℝ).hasFDerivAt_of_bilinear mother inverseField
  have adjoint := LAlanineSpatialProjection.adjointReal.hasFDerivAt.comp positions mother
  have full := ((compL ℂ SpinSpace (CoefficientSpace state) SpinSpace).bilinearRestrictScalars ℝ).hasFDerivAt_of_bilinear first adjoint
  have smooth : DifferentiableAt ℝ (fun next =>
      (frameAt state next ∘L Ring.inverse (gramAt state next)) ∘L (frameAt state next).adjoint) positions :=
    full.differentiableAt
  have same : (fun next => (frameAt state next ∘L Ring.inverse (gramAt state next)) ∘L
      (frameAt state next).adjoint) = projectionAt state := by
    funext next
    simp only [projectionAt,LAlanineSpatialProjection.totalProjection,gramAt,comp_assoc]
  rw [same] at smooth
  exact smooth.hasFDerivAt

theorem projection_source (state : CPS1ElectronicSource.State frame) :
    projectionAt state (sourcePositions state) = CPS1MolecularFrame.currentProjection state := by
  rw [projectionAt,frame_source,LAlanineSpatialProjection.total_projection_source]
  rfl

theorem configuration_line_hasDerivAt (state : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration state) :
    HasDerivAt (fun time : ℝ => positions + time • direction) direction 0 := by
  have source := (hasDerivAt_const (0 : ℝ) positions).add ((hasDerivAt_id 0).smul_const direction)
  simpa only [one_smul,zero_add] using! source

theorem projection_fderiv_apply (state : CPS1ElectronicSource.State frame)
    (direction : NuclearConfiguration state) :
    projectionFDeriv state direction = LAlanineSpatialProjection.projectionRate
      (frameAt state (sourcePositions state)) (frameFDeriv state (sourcePositions state) direction)
      (source_gram_unit state) := by
  let curve := fun time : ℝ => sourcePositions state + time • direction
  have motion : HasDerivAt curve direction 0 := configuration_line_hasDerivAt state _ _
  have mother : HasDerivAt (fun time => frameAt state (curve time))
      (frameFDeriv state (sourcePositions state) direction) 0 := by
    have source := (frame_hasFDerivAt state (curve 0)).comp_hasDerivAt 0 motion
    simpa only [Function.comp_def,curve,zero_smul,add_zero] using! source
  have unit : IsUnit (LAlanineSpatialProjection.gram (frameAt state (curve 0))) := by
    simpa only [curve,zero_smul,add_zero] using source_gram_unit state
  have read := LAlanineSpatialProjection.total_projection_curve_derivative
    (fun time => frameAt state (curve time)) _ 0 mother unit
  have atCurve : HasFDerivAt (projectionAt state) (projectionFDeriv state) (curve 0) := by
    simpa only [curve,zero_smul,add_zero] using projection_hasFDerivAt state
  have generated := atCurve.comp_hasDerivAt 0 motion
  have result := generated.unique read
  simpa only [Function.comp_def,curve,zero_smul,add_zero] using result

theorem source_projection_rate (state : CPS1ElectronicSource.State frame) :
    projectionFDeriv state (sourceVelocity state) = CPS1MolecularFrame.currentProjectionRate state := by
  have atSource : HasFDerivAt (projectionAt state) (projectionFDeriv state) (sourceLine state 0) := by
    rw [source_line_initial]
    exact projection_hasFDerivAt state
  have actual : HasDerivAt
      (fun time => LAlanineSpatialProjection.totalProjection (CPS1MolecularFrame.frameCurve state time))
      (projectionFDeriv state (sourceVelocity state)) 0 := by
    have source := atSource.comp_hasDerivAt 0 (source_line_hasDerivAt state 0)
    simpa only [Function.comp_def,projectionAt,frame_line] using source
  exact actual.unique (CPS1MolecularFrame.source_projection_derivative state)

end
end CPS1Deformation
