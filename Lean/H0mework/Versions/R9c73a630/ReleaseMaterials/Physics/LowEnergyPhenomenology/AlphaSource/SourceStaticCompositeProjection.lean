import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedPhotonCoupling
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticActualPole

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalDressedPhotonCouplingReturn PreparationPhysicalDressedGTVertexReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumFieldCovector
open PreparationVacuumSourceActionJets PreparationVacuumSourceFieldFamily PreparationVacuumActionDecomposition
open PreparationVacuumActionFieldLift PreparationVacuumFullFieldRiesz PreparationVacuumMixedFieldReturn
open PreparationVacuumSourcePreparedResponse PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumLowerClassical PreparationVacuumNonlinearFieldCurve
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open GaussFockLift GaussHistoryHilbert GaussFockPair GaussDensityCore CanonicalGradedSpatialSource CanonicalPhysicalYResolvent
open GaussComposite GaussComposite.SourceGraph MeasureTheory Filter Set
open GaussUnitaryHistory (Index)
open scoped BigOperators InnerProductSpace ContDiff Topology Matrix Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ FiberOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

/-- The complete field form only forgets directions whose original slice vector is zero. -/
theorem sourceStaticFieldForm_congr (f g : Field289) (same : fieldVector f=fieldVector g)
    (p : PhysicalMomentum) (a b : QuantumTest) : fieldForm f p a b=fieldForm g p a b := by
  have curve : fieldCoordinateCurve f=fieldCoordinateCurve g := by
    funext r z
    simp only [fieldCoordinateCurve,same]
  funext r
  simp only [fieldForm,nativeFieldForm,coframeFieldForm,mixedFieldForm,rowFieldForm,fiberFieldForm,curve]

theorem sourceStaticFieldJet_congr (f g : Field289) (same : fieldVector f=fieldVector g)
    (p : PhysicalMomentum) (a b : QuantumTest) :
    (fieldJets f p a b).first 0=(fieldJets g p a b).first 0 := by
  have derivative:=(fieldJets f p a b).actual.1
  have moved:=derivative.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun r=>
    (congrFun (sourceStaticFieldForm_congr f g same p a b) r).symm))
  exact moved.unique (fieldJets g p a b).actual.1

private theorem coframe_zero (f : Field289) (zero : fieldCoframe f=0) (z : SourceCoordinateSlice) :
    coframeSliceDirection f z=0 := by
  simp only [coframeSliceDirection,coframeResidual,normalizedCoframe,zero,zero_mul,map_zero,sub_self]

private theorem inactive_vector (i : Fin 289) (inactive : (73 : ℕ) ≤ i.val) (z : SourceCoordinateSlice) :
    fieldVector (fieldBasis i) z=0 := by
  have scalar : fieldScalar (fieldBasis i)=0 := by
    have slot (j : Fin 9) : scalarSlot j≠i := by intro h; have h':=congrArg Fin.val h; simp only [scalarSlot] at h'; omega
    simp only [fieldScalar,fieldBasis,Pi.single_apply,slot,if_false,zero_smul,Finset.sum_const_zero]
  have gauge (mu : Fin 4) : fieldGauge (fieldBasis i) mu=0 := by
    have slot (j : Fin 12) : gaugeSlot mu j≠i := by intro h; have h':=congrArg Fin.val h; simp only [gaugeSlot] at h'; omega
    simp only [fieldGauge,fieldBasis,Pi.single_apply,slot,if_false,zero_smul,Finset.sum_const_zero]
  have coframe : fieldCoframe (fieldBasis i)=0 := by
    funext a mu
    have slot : coframeSlot a mu≠i := by intro h; have h':=congrArg Fin.val h; simp only [coframeSlot] at h'; omega
    simp only [fieldCoframe,fieldBasis,Pi.single_apply,slot,if_false]
    rfl
  have ambient : fieldAmbient (fieldBasis i)=0 := by
    apply Prod.ext
    · exact scalar
    · apply PiLp.ext
      intro j
      exact gauge j.succ
  simp only [fieldVector,gaugeParameters,ambient,map_zero,coframe_zero _ coframe,Prod.snd_zero,Prod.mk_zero_zero]

private theorem zero_vector (z : SourceCoordinateSlice) : fieldVector (0:Field289) z=0 := by
  have cf : fieldCoframe (0:Field289)=0 := rfl
  have ambient : fieldAmbient (0:Field289)=0 := fieldAmbientLinear.map_zero
  simp only [fieldVector,gaugeParameters,ambient,map_zero,coframe_zero _ cf,Prod.snd_zero,Prod.mk_zero_zero]

private theorem zero_first (p : PhysicalMomentum) (a b : QuantumTest) :
    (fieldJets (0:Field289) p a b).first 0=0 := by
  have curve (r : ℝ) (z : SourceCoordinateSlice) : fieldCoordinateCurve (0:Field289) r z=z := by
    simp only [fieldCoordinateCurve,zero_vector,smul_zero,add_zero]
  have same : fieldForm (0:Field289) p a b=fun _=>fieldForm (0:Field289) p a b 0 := by
    funext r
    simp only [fieldForm,nativeFieldForm,coframeFieldForm,mixedFieldForm,rowFieldForm,fiberFieldForm,curve]
  have derivative:=(fieldJets (0:Field289) p a b).actual.1
  have moved:=derivative.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun r=>(congrFun same r).symm))
  exact moved.unique (hasDerivAt_const 0 _)

/-- Actual matter, independent dual and auxiliary columns have no slice insertion in this original current. -/
theorem sourceStaticComposite_inactive (i : Fin 289) (inactive : (73 : ℕ) ≤ i.val)
    (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum) (F : Index) (cut : ℕ)
    (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    preparedCovector epsilon precision p k F cut z w left right a s b t i=0 := by
  change preparedCurrent epsilon precision (fieldBasis i) p k F cut z w left right a s b t=0
  rw [preparedCurrent_source]
  have same : fieldVector (fieldBasis i)=fieldVector 0 := by
    funext x
    rw [inactive_vector i inactive,zero_vector]
  rw [sourceStaticFieldJet_congr _ _ same,zero_first]

/-- The same original spatial gauge direction remains live on every configuration. -/
def sourceStaticCompositeGauge : Field289:=fieldBasis 21-fieldBasis 34

def sourceStaticCompositeWeight (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : ℂ :=
  (3/10:ℂ)*rootTwo*(preparedCovector epsilon precision p k F cut z w left right a s b t 21-
    preparedCovector epsilon precision p k F cut z w left right a s b t 34)

private theorem origin_table : fullNativeOriginTerms=[
  ⟨21,0,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨21,1,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨34,0,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨34,1,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨74,2,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨76,2,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨80,3,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨82,3,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨86,4,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨88,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨88,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨88,4,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨92,0,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨92,4,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨94,1,⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩⟩,
  ⟨94,4,⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩⟩,
  ⟨98,3,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨100,3,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨104,2,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨106,2,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨110,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨110,4,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨112,1,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨112,4,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨116,4,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
  ⟨118,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨118,1,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨118,4,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
  ⟨217,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩⟩,
  ⟨217,1,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩⟩,
  ⟨230,0,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩⟩,
  ⟨230,1,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩⟩] := by decide +kernel

private theorem origin_read (v : Fin 289→ℂ) (zero : ∀i : Fin 289,(73 : ℕ) ≤ i.val→v i=0) :
    fullNativeOrigin.transpose*ᵥv=
      Pi.single 0 ((3/10:ℂ)*rootTwo*(v 21-v 34))+Pi.single 1 ((3/10:ℂ)*rootTwo*(v 21-v 34)) := by
  rw [fullNativeOrigin_generated,origin_table]
  norm_num [sourceMatrix,SourceTerm.matrix,Matrix.transpose_add,Matrix.transpose_single,Matrix.transpose_zero,
    Matrix.add_mulVec,Matrix.zero_mulVec,Matrix.single_mulVec,Powers.value,coefficientValue]
  simp (disch:=norm_num) only [zero]
  ext i
  simp only [Pi.single_apply,Function.update_apply,Pi.zero_apply,Pi.add_apply]
  split_ifs <;> ring

/-- Full original origin projection on the actual composite source, without an old held-current premise. -/
theorem sourceStaticComposite_origin (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    fullNativeOrigin.transpose*ᵥpreparedCovector epsilon precision p k F cut z w left right a s b t=
      Pi.single 0 (sourceStaticCompositeWeight epsilon precision p k F cut z w left right a s b t)+
      Pi.single 1 (sourceStaticCompositeWeight epsilon precision p k F cut z w left right a s b t) := by
  exact origin_read _ (fun i hi=>sourceStaticComposite_inactive i hi epsilon precision p k F cut z w left right a s b t)

end LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn
