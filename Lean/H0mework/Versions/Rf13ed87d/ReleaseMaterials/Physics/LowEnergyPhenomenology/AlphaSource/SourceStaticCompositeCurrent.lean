import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticCompositeProjection

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
open GaussNativePotential
open GaussUnitaryHistory (Index)
open scoped BigOperators InnerProductSpace ContDiff Topology Matrix Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ FiberOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open StageNineP286GaugeConnectionVariationDensity
open Electromagnetic.CanonicalCoframe FullQuantum.CoframeResponse FullQuantum.StateGreen

private theorem gauge_field : sourceStaticCompositeGauge=gaugeField 1 0-gaugeField 2 1 := rfl

/-- The unscaled surviving source direction is exactly two original spatial gauge slots. -/
theorem sourceStaticCompositeGauge_slots :
    fieldScalar sourceStaticCompositeGauge=0 ∧ fieldCoframe sourceStaticCompositeGauge=0 ∧
    ∀mu : Fin 4,fieldGauge sourceStaticCompositeGauge mu=
      (if mu=1 then originalUnit 0 else 0)-(if mu=2 then originalUnit 1 else 0) := by
  rw [gauge_field]
  constructor
  · simp only [fieldScalar,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
    change fieldScalar (gaugeField 1 0)-fieldScalar (gaugeField 2 1)=0
    rw [gauge_scalar,gauge_scalar,sub_self]
  constructor
  · change fieldCoframe (gaugeField 1 0)-fieldCoframe (gaugeField 2 1)=0
    rw [gauge_coframe,gauge_coframe,sub_self]
  · intro mu
    simp only [fieldGauge,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib,gauge_gauge_slot]
    fin_cases mu <;> simp

/-- The original slice reconstruction retains the scalar compensation at every physical configuration. -/
theorem sourceStaticCompositeGauge_scalarBalance (z : physicalChart) :
    scalarP286ActionBilinear (gaugeOrbitParameter sourceStaticCompositeGauge z.val) (scalarField z.val)+
      ((gaugeParameters sourceStaticCompositeGauge z.val).2.1:Scalar)=0 := by
  rw [scalar_tangent_reconstruction,sourceStaticCompositeGauge_slots.1]

/-- The matrix is computed from the two original gauge-density columns, before any external-state restriction. -/
def sourceStaticCompositeMother (p : PhysicalMomentum) (s : ActionState) : FullMatrix :=
  -fourierLinear p (fun i=>statePhase s*(if i=0 then stateVolume s •
    (coefficientMatrix 1 s.1*GaussNativeMatter.nativePrimal (originalUnit 0)) else 0))+
  fourierLinear p (fun i=>statePhase s*(if i=0 then stateVolume s •
    (coefficientMatrix 2 s.1*GaussNativeMatter.nativePrimal (originalUnit 1)) else 0))

theorem sourceStaticCompositeMother_generated (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    symbolFirst p s (fieldDirection sourceStaticCompositeGauge)=sourceStaticCompositeMother p s := by
  have direction : fieldDirection sourceStaticCompositeGauge=
      fieldDirection (gaugeField 1 0)-fieldDirection (gaugeField 2 1) :=
    congrArg fieldDirection gauge_field |>.trans (fieldDirectionLinear.map_sub _ _)
  rw [symbolFirst,direction,map_sub]
  change symbolFirst p s (fieldDirection (gaugeField 1 0))-symbolFirst p s (fieldDirection (gaugeField 2 1))=_
  rw [symbolFirst_field _ p s valid,symbolFirst_field _ p s valid]
  simp_rw [gauge_density _ _ s valid.1]
  simp only [sourceStaticCompositeMother,sub_neg_eq_add]

def sourceStaticCompositeMatter (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ :=
  densityCurrent sourceStaticCompositeGauge p a b z+
    pairSample z (a z) (quantizer (sourceStaticCompositeMother p (sourceState z)) (b z))-
    pairSample z (a z) (quantizer (symbolFirst p (sourceState z) (complement sourceStaticCompositeGauge z)) (b z))

private theorem matter_sample (p : PhysicalMomentum) (a b : QuantumTest) (z : physicalChart) :
    sampleCurrent (fiberSample (actualFiber p) a b) sourceStaticCompositeGauge z.val=
      sourceStaticCompositeMatter p a b z.val := by
  have whole:=fiber_sample_mother_balance sourceStaticCompositeGauge p a b z
  have matrix:=symbolFirst_actual sourceStaticCompositeGauge p z
  rw [sourceStaticCompositeMother_generated _ _ (sourceState_valid z)] at matrix
  have pair:=congrArg (fun A : PreparationVacuumSourceFieldFamily.FiberMap=>pairSample z.val (a z.val) (A (b z.val))) matrix
  simp only [neg_apply,pairSample,PiLp.neg_apply,mul_neg,Finset.sum_neg_distrib] at pair
  change pairSample z.val (a z.val) (quantizer (sourceStaticCompositeMother p (sourceState z.val)) (b z.val))=
    -pairSample z.val (a z.val) (fiberFamily sourceStaticCompositeGauge p z.val (b z.val)) at pair
  change _=densityCurrent _ p a b z.val+pairSample z.val (a z.val)
    (quantizer (sourceStaticCompositeMother p (sourceState z.val)) (b z.val))-_
  rw [pair]
  linear_combination whole

private theorem matter_parameter (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    parameterCurrent (fiberSample (actualFiber p) a b) sourceStaticCompositeGauge z=
      sourceStaticCompositeMatter p a b z := by
  rw [parameterCurrent_eq (fiberSample (actualFiber p) a b) a
    (fun g r z hz hx=>fiberSample_param (actualFiber p) (actualFiber_smooth p) a b
      (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd (r,z) hx
      (field_curve_smooth g r ⟨z,hz⟩) contDiffAt_snd)
    (fun z=>(fiberSample_param (actualFiber p) (actualFiber_smooth p) a b id (fun _=>z.val)
      z.val z.property contDiffAt_id contDiffAt_const).differentiableAt (by simp))
    (fiberSample_zero_outside (actualFiber p) a b)]
  by_cases inside : z∈tsupport a
  · exact matter_sample p a b ⟨z,a.tsupport_subset inside⟩
  · have zero : a z=0:=image_eq_zero_of_notMem_tsupport inside
    have same : fiberSample (actualFiber p) a b z=fun _=>0 :=
      funext (fun x=>fiberSample_zero_outside (actualFiber p) a b z x inside)
    simp only [sampleCurrent,same,fderiv_const_apply,zero_apply]
    simp only [sourceStaticCompositeMatter,densityCurrent,zero,pairSample,PiLp.zero_apply,star_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,add_zero,sub_zero]

theorem sourceStaticCompositeMatter_integrable (p : PhysicalMomentum) (a b : QuantumTest) :
    Integrable (sourceStaticCompositeMatter p a b) GaussHistoryHilbert.configurationMeasure := by
  rw [←funext (matter_parameter p a b)]
  exact parameterCurrent_integrable (fiberSample (actualFiber p) a b) a
    (fun g r z hz hx=>fiberSample_param (actualFiber p) (actualFiber_smooth p) a b
      (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd (r,z) hx
      (field_curve_smooth g r ⟨z,hz⟩) contDiffAt_snd)
    (fiberSample_zero_outside (actualFiber p) a b) sourceStaticCompositeGauge

/-- Original native, coframe, density, complementary scalar/gauge and retained-Y terms all survive. -/
def sourceStaticCompositeConfiguration (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  (nativeFieldJets sourceStaticCompositeGauge a b).first 0+
    (coframeFieldJets sourceStaticCompositeGauge a b).first 0+
    (∫z,sourceStaticCompositeMatter p a b z ∂GaussHistoryHilbert.configurationMeasure)-
    (fiberFieldJets sourceStaticCompositeGauge retainedCoefficient retainedCoefficient_smooth a b).first 0

theorem sourceStaticCompositeConfiguration_generated (p : PhysicalMomentum) (a b : QuantumTest) :
    (fieldJets sourceStaticCompositeGauge p a b).first 0=sourceStaticCompositeConfiguration p a b := by
  change _+_+(∫z,parameterCurrent (fiberSample (actualFiber p) a b) sourceStaticCompositeGauge z
    ∂GaussHistoryHilbert.configurationMeasure)-_=_
  unfold sourceStaticCompositeConfiguration
  rw [funext (matter_parameter p a b)]

private theorem gauge_read (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    preparedCurrent epsilon precision sourceStaticCompositeGauge p k F cut z w left right a s b t=
      preparedCovector epsilon precision p k F cut z w left right a s b t 21-
        preparedCovector epsilon precision p k F cut z w left right a s b t 34 := by
  rw [prepared_covector_coordinates]
  simp only [sourceStaticCompositeGauge,fieldBasis,Pi.sub_apply]
  let v : Fin 289 → ℂ := fun x =>
    preparedCovector epsilon precision p k F cut z w left right a s b t x
  change (∑ x : Fin 289,
      (↑((Pi.single (M := fun _ : Fin 289 => ℝ) (21 : Fin 289) (1 : ℝ) x)-
        Pi.single (M := fun _ : Fin 289 => ℝ) (34 : Fin 289) (1 : ℝ) x) : ℂ)*v x)=
      v 21-v 34
  have cast_sub (x : Fin 289) :
      ((↑((Pi.single (M := fun _ : Fin 289 => ℝ) (21 : Fin 289) (1 : ℝ) x)-
        Pi.single (M := fun _ : Fin 289 => ℝ) (34 : Fin 289) (1 : ℝ) x) : ℂ))=
        ((↑(Pi.single (M := fun _ : Fin 289 => ℝ) (21 : Fin 289) (1 : ℝ) x) : ℂ)-
          (↑(Pi.single (M := fun _ : Fin 289 => ℝ) (34 : Fin 289) (1 : ℝ) x) : ℂ)) := by
    norm_num
  simp_rw [cast_sub,sub_mul,Finset.sum_sub_distrib]
  have cast_ite (i x : Fin 289) :
      ((↑(Pi.single (M := fun _ : Fin 289 => ℝ) i (1 : ℝ) x) : ℂ))=
        (if x=i then (1:ℂ) else 0) := by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  simp_rw [cast_ite]
  simp only [ite_mul,one_mul,zero_mul]
  have h21:=Fintype.sum_ite_eq (21 : Fin 289) v
  have h34:=Fintype.sum_ite_eq (34 : Fin 289) v
  have h21' : (∑ x,if x=21 then v x else 0)=v 21 := by
    convert h21 using 1
    simp [eq_comm]
  have h34' : (∑ x,if x=34 then v x else 0)=v 34 := by
    convert h34 using 1
    simp [eq_comm]
  rw [h21',h34']

theorem sourceStaticCompositeWeight_generated (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    sourceStaticCompositeWeight epsilon precision p k F cut z w left right a s b t=
      (3/10:ℂ)*rootTwo*sourceStaticCompositeConfiguration p
        (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint (completedLeg left a s (sourceProfile epsilon precision))))
        (sourceTestApprox F (finiteFull p F cut w (completedLeg right b t (sourceProfile epsilon precision)))) := by
  rw [sourceStaticCompositeWeight,←gauge_read,preparedCurrent_source,sourceStaticCompositeConfiguration_generated]

theorem sourceStaticCompositeWeight_price (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (a s b t : Fin 2) :
    ‖sourceStaticCompositeWeight epsilon precision p k F cut z w left right a s b t‖≤
      ‖(3/10:ℂ)*rootTwo‖*(‖completedLeg left a s (sourceProfile epsilon precision)‖*
        (normBound cut z*currentPrice sourceStaticCompositeGauge p F*normBound cut w)*
          ‖completedLeg right b t (sourceProfile epsilon precision)‖) := by
  rw [sourceStaticCompositeWeight,←gauge_read,norm_mul]
  exact mul_le_mul_of_nonneg_left (preparedCurrent_price epsilon precision sourceStaticCompositeGauge
    p k F cut z w hz hw left right a s b t) (norm_nonneg _)

private theorem static_inverse_pair (w : ℂ) : staticInverse*ᵥ(Pi.single 0 w+Pi.single 1 w)=
    Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*w)+
      Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*w) := by
  norm_num [staticInverse,staticInverseTerms,sourceMatrix,SourceTerm.matrix,Powers.value,coefficientValue,
    Matrix.add_mulVec,Matrix.zero_mulVec,Matrix.single_mulVec,Pi.add_apply,Pi.single_apply,Fin.ext_iff]
  congr 1

private theorem transpose_read (M : Matrix (Fin 289) (Fin 289) ℂ) (v w : Fin 289→ℂ) :
    (∑i,v i*(M*ᵥw) i)=∑j,(M.transpose*ᵥv) j*w j := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full static residue is consumed by two independent original composite preparations. -/
private theorem leading_weight
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
      staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)=
    -((9/125+67/72:ℂ)*rootTwo*rootFifteen)*
      sourceStaticCompositeWeight epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD*
      sourceStaticCompositeWeight epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS := by
  unfold staticResidue
  rw [transpose_read,sourceStaticComposite_origin,sourceStaticComposite_origin,static_inverse_pair]
  simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib,Pi.single_apply,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  norm_num
  ring

/-- The leading static tensor directly consumes both computed full configuration integrals. -/
theorem sourceStaticCompositeLeading_return
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
      staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)=
    -((9/125+67/72:ℂ)*rootTwo*rootFifteen)*
      ((3/10:ℂ)*rootTwo*sourceStaticCompositeConfiguration pD
        (sourceTestApprox FD ((finiteFull (pD+kD) FD cutD zD).adjoint (completedLeg lD aD sD (sourceProfile epsD precD))))
        (sourceTestApprox FD (finiteFull pD FD cutD wD (completedLeg rD bD tD (sourceProfile epsD precD)))))*
      ((3/10:ℂ)*rootTwo*sourceStaticCompositeConfiguration pS
        (sourceTestApprox FS ((finiteFull (pS+kS) FS cutS zS).adjoint (completedLeg lS aS sS (sourceProfile epsS precS))))
        (sourceTestApprox FS (finiteFull pS FS cutS wS (completedLeg rS bS tS (sourceProfile epsS precS))))) := by
  rw [leading_weight,sourceStaticCompositeWeight_generated,sourceStaticCompositeWeight_generated]

end LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn
