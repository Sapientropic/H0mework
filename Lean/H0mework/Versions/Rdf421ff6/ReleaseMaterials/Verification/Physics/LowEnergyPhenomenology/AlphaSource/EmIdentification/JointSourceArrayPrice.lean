import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.NativeActualLegPrice
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationJointMixedResponse
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSpatialFullFormFeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceMixed289ResponseOwn
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open PreparationVacuumGradedTransport PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open PreparationVacuumSpatialDensityTransport PreparationVacuumJointFieldResponse
open CanonicalGradedLocalCurrent PreparationVacuumActionFieldLift
open ActualQuantitativePreparedFrameOwn ActualNativePreparedLegPriceOwn
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped Topology InnerProductSpace BigOperators
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] physicalBasis physicalFrame bareTest sourceProfile actualPrepared actualFullY jointCurrent jointHessian

private def originalAssemblyPrice (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (entries : PhysicalBasisIndex p F → PhysicalBasisIndex p F → ℂ) : ℝ :=
  ∑ grade : NativeHistoryGrade.Label, ∑ i : PhysicalBasisIndex p F, ∑ j : PhysicalBasisIndex p F,
    ‖entries i j‖ * ‖physicalFrame p F (grade,i)‖ * ‖physicalFrame p F (grade,j)‖

private theorem originalAssembly_bound (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (entries : PhysicalBasisIndex p F → PhysicalBasisIndex p F → ℂ) :
    ‖sourceAssembly p F entries‖ ≤ originalAssemblyPrice p F entries := by
  unfold sourceAssembly originalAssemblyPrice
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro grade _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_smul, InnerProductSpace.norm_rankOne, mul_assoc, le_refl]

def originalCompactYPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (r : ℝ) : ℝ :=
  ‖(uncutTest f (finiteRetainer p F) r : BoundedContinuousFunction SourceCoordinateSlice PreparationVacuumUncutYukawa.Fiber)‖

theorem originalCompactY_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (r : ℝ) :
    ‖uncutOperator f (finiteRetainer p F) r‖ ≤ originalCompactYPrice f p F r := by
  unfold uncutOperator originalCompactYPrice
  exact GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

def originalJointCurrentPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  originalAssemblyPrice p F (fun i j => (completeJets f p (bareTest p F i) (bareTest p F j)).first 0) +
    originalCompactYPrice f p F 1 + originalCompactYPrice f p F 0

def originalJointContactPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  originalAssemblyPrice p F (fun i j => (completeJets f p (bareTest p F i) (bareTest p F j)).second)

theorem originalJointCurrent_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    ‖jointCurrent p F z 0 f‖ ≤ originalJointCurrentPrice f p F := by
  rw [jointCurrent_source, sourceCurrent_complete]
  change ‖sourceAssembly p F (fun i j => (completeJets f p (bareTest p F i) (bareTest p F j)).first 0) +
    (uncutOperator f (finiteRetainer p F) 1 - uncutOperator f (finiteRetainer p F) 0)‖ ≤ _
  unfold originalJointCurrentPrice
  rw [add_assoc]
  exact (norm_add_le _ _).trans (add_le_add (originalAssembly_bound p F _)
    ((norm_sub_le _ _).trans (add_le_add (originalCompactY_price f p F 1) (originalCompactY_price f p F 0))))

theorem originalJointContact_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    ‖jointHessian p F z f f‖ ≤ originalJointContactPrice f p F := by
  rw [jointHessian_source_diagonal, sourceContact_complete]
  change ‖sourceAssembly p F (fun i j => (completeJets f p (bareTest p F i) (bareTest p F j)).second) + 0‖ ≤ _
  rw [add_zero]
  exact originalAssembly_bound p F _

private theorem symmetric_polarization {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (Q : E →L[ℝ] E →L[ℝ] V) (f g : E) (symm : Q g f = Q f g) :
    Q f g = (1/2 : ℝ) • (Q (f+g) (f+g) - Q f f - Q g g) := by
  simp only [map_add, add_apply, symm]
  module

theorem originalJointHessian_polarization (f g : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointHessian p F z f g = (1/2 : ℝ) •
      (jointHessian p F z (f+g) (f+g) - jointHessian p F z f f - jointHessian p F z g g) := by
  exact symmetric_polarization (jointHessian p F z) f g (jointHessian_symmetric p F z g f)

def originalJointCrossContactPrice (f g : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  (originalJointContactPrice (f+g) p F + originalJointContactPrice f p F + originalJointContactPrice g p F) / 2

private theorem symmetric_polarization_bound {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : E →L[ℝ] E →L[ℝ] V) (f g : E) (symm : Q g f = Q f g)
    (total left right : ℝ) (ht : ‖Q (f+g) (f+g)‖ ≤ total) (hl : ‖Q f f‖ ≤ left) (hr : ‖Q g g‖ ≤ right) :
    ‖Q f g‖ ≤ (total + left + right) / 2 := by
  rw [symmetric_polarization Q f g symm]
  have halfNorm : ‖(1/2 : ℝ)‖ = 1/2 := by norm_num
  rw [norm_smul, halfNorm]
  have price := (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ht hl)) hr)
  exact (mul_le_mul_of_nonneg_left price (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq (by ring)

theorem originalJointHessian_price (f g : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    ‖jointHessian p F z f g‖ ≤ originalJointCrossContactPrice f g p F :=
  symmetric_polarization_bound (jointHessian p F z) f g (jointHessian_symmetric p F z g f)
    _ _ _ (originalJointContact_price (f+g) p F z) (originalJointContact_price f p F z)
      (originalJointContact_price g p F z)

end LowEnergy.ActualSourceMixed289ResponseOwn
