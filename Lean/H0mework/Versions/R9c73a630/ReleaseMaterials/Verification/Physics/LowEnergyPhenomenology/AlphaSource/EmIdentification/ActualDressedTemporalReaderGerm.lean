import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorConstraint
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNonlinearPolarization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalHalf
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open FullQuantum.StateGreen PreparationVacuumFixedMomentumActionReturn PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization SourceQuantumFockGauge PreparationVacuumNonlinearFieldCurve
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction
open PreparationVacuumLowerClassical PreparationVacuumTemporalCharge PreparationVacuumGaugeSourceInjection
open PreparationVacuumNoetherChart PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open SourcePropagationNativeActionHessian GaussNativeMatter GaussCoreHilbert
open ActualDressedNativeConstraint ActualDressedNullNative ActualDressedLockedWard ActualDressedConstraintRead
open ActualDressedTemporalCurrent PreparationVacuumWeightedChargeActionWard
open Filter
open scoped Matrix BigOperators Topology Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] nativeSourceColumn noetherReader nativeReader nativeReaderContact

open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumNonlinearFieldCurve PreparationVacuumHalfDensityFiber
open MeasureTheory Set
open scoped InnerProductSpace
private abbrev TemporalOp:=H→L[ℂ]H
local instance : NormedAlgebra ℝ TemporalOp:=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationPhysicalActionUnits PreparationVacuumElectricConstraint CanonicalGradedCharge
open PreparationVacuumSourceChargeWard GaussFockPair PreparationVacuumFieldConstraintResponse

/-- A common radius from exactly the original source frame tests; it remains positive for the empty frame. -/
def temporalFrameRadius (F : GaussUnitaryHistory.Index) : ℝ:=
  (1+∑i : FrameIndex F,(ambientRadius (frameTest F i))⁻¹)⁻¹

theorem temporal_frame_radius_positive (F : GaussUnitaryHistory.Index) : 0<temporalFrameRadius F :=by
  apply inv_pos.mpr
  have terms : 0 ≤ ∑i : FrameIndex F,(ambientRadius (frameTest F i))⁻¹ :=
    Finset.sum_nonneg (fun i _=>inv_nonneg.mpr (ambientRadius_positive (frameTest F i)).le)
  linarith

theorem temporal_frame_radius_le (F : GaussUnitaryHistory.Index) (i : FrameIndex F) :
    temporalFrameRadius F ≤ ambientRadius (frameTest F i) :=by
  let S : ℝ:=1+∑j : FrameIndex F,(ambientRadius (frameTest F j))⁻¹
  have terms : 0 ≤ ∑j : FrameIndex F,(ambientRadius (frameTest F j))⁻¹ :=
    Finset.sum_nonneg (fun j _=>inv_nonneg.mpr (ambientRadius_positive (frameTest F j)).le)
  have positive : 0<S:=by dsimp [S];linarith
  have oneTerm : (ambientRadius (frameTest F i))⁻¹ ≤ S :=by
    have term:=Finset.single_le_sum (fun j (_ : j∈Finset.univ)=>
      inv_nonneg.mpr (ambientRadius_positive (frameTest F j)).le) (Finset.mem_univ i)
    dsimp [S]
    linarith
  change S⁻¹ ≤ ambientRadius (frameTest F i)
  apply (mul_le_mul_iff_right₀ positive).mp
  rw [mul_inv_cancel₀ positive.ne']
  calc
    1=ambientRadius (frameTest F i)*(ambientRadius (frameTest F i))⁻¹:=
      (mul_inv_cancel₀ (ambientRadius_positive (frameTest F i)).ne').symm
    _≤S*ambientRadius (frameTest F i):=by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left oneTerm (ambientRadius_positive (frameTest F i)).le

private theorem temporal_form_constant (a : Fin 12) (p : PhysicalMomentum) (l r : QuantumTest)
    (h : Field289) (small : ‖h‖<ambientRadius l) :
    noetherForm (temporalField a) p l r h=weightedTemporalForm a l r :=by
  unfold noetherForm weightedTemporalForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases inside : z∈tsupport l
  · have valid:=ambientRadius_valid l h z small.le inside
    change pairSample z (l z)
      (quantizer (transportedRawSymbol (temporalField a) (sourceState z) (ambientState (h,z)) p) (r z))=_
    rw [transportedTemporalSymbol a (sourceState z) (ambientState (h,z)) valid p]
  · dsimp only
    rw [noetherSample_zero (temporalField a) p l r h z inside]
    simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

/-- One source radius pays every temporal Lie direction and every spatial momentum on the same full field ball. -/
theorem temporal_reader_constant (F : GaussUnitaryHistory.Index) (h : Field289)
    (small : ‖h‖<temporalFrameRadius F) (a : Fin 12) (p : PhysicalMomentum) :
    noetherReader (temporalField a) p F h=noetherReader (temporalField a) p F 0 :=by
  rw [temporalReader_source]
  unfold noetherReader
  apply congrArg (finiteRiesz F)
  funext i j
  exact temporal_form_constant a p (frameTest F i) (frameTest F j) h
    (small.trans_le (temporal_frame_radius_le F i))

theorem temporal_reader_common_germ (F : GaussUnitaryHistory.Index) :
    ∀ᶠh : Field289 in 𝓝 0,∀a : Fin 12,∀p : PhysicalMomentum,
      noetherReader (temporalField a) p F h=noetherReader (temporalField a) p F 0 :=by
  have near : ∀ᶠh : Field289 in 𝓝 0,‖h‖<temporalFrameRadius F:=
    (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using temporal_frame_radius_positive F))
  exact near.mono (fun h small a p=>temporal_reader_constant F h small a p)

/-- The source operator contains the original time weight, full Gauss orbit, and normal-order pair before any state read. -/
def temporalGaussReader (F : GaussUnitaryHistory.Index) (a : Fin 12) : TemporalOp:=
  finiteRiesz F (fun i j=>sourcePair (frameTest F i)
      (sourceTimeWeightCore (orbitAction (originalUnit a) (frameTest F j)))+
    sourcePair (frameTest F i) (normalChargeCore a (frameTest F j)))

private theorem riesz_neg (F : GaussUnitaryHistory.Index) (A : FrameIndex F→FrameIndex F→ℂ) :
    finiteRiesz F (fun i j=> -A i j)= -finiteRiesz F A :=by
  simp only [finiteRiesz,neg_smul,Finset.sum_neg_distrib]

/-- The sign is the original Gauss constraint chargeAction = -orbitAction. -/
theorem temporal_reader_gauss (F : GaussUnitaryHistory.Index) (h : Field289)
    (small : ‖h‖<temporalFrameRadius F) (a : Fin 12) (p : PhysicalMomentum) :
    noetherReader (temporalField a) p F h= -temporalGaussReader F a :=by
  rw [temporal_reader_constant F h small a p,temporalReader_core]
  have forms (i j : FrameIndex F) : sourcePair (frameTest F i) (rawChargeCore a (frameTest F j))=
      -(sourcePair (frameTest F i) (sourceTimeWeightCore (orbitAction (originalUnit a) (frameTest F j)))+
        sourcePair (frameTest F i) (normalChargeCore a (frameTest F j))) :=by
    rw [rawChargeCore_source,original_temporal_weight_core,original_gauss_constraint]
    simp only [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.neg_apply,sourcePair,
      map_sub,map_neg,inner_sub_right,inner_neg_right]
    abel
  have same:=congrArg (finiteRiesz F) (funext (fun i=>funext (fun j=>forms i j)))
  exact same.trans (riesz_neg F _)

end LowEnergy.GaussComposite.ActualDressedTemporalHalf
