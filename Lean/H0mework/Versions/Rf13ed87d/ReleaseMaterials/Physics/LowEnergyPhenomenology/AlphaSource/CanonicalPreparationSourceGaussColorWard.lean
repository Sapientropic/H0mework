import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussKineticTorque

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalGaussColorTorque
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore




open scoped ContDiff


private theorem core_separates (x : QuantumTest) (h : ∀ f,sourcePair f x=0) : x=0 := by
  apply embed_injective
  rw [map_zero]
  exact inner_self_eq_zero.mp (h x)

private theorem colour_adjoint (P A : QuantumEnd)
    (paired : ∀ f g,sourcePair f (A g)=sourcePair (P f) g)
    (commutes : ∀ f,P (chargeAction (colorGenerator 2) f)=chargeAction (colorGenerator 2) (P f)) :
    ∀ f,A (chargeAction (colorGenerator 2) f)=chargeAction (colorGenerator 2) (A f) := by
  intro g
  apply sub_eq_zero.mp
  apply core_separates
  intro f
  simp only [sourcePair,map_sub,inner_sub_right]
  change sourcePair f (A (chargeAction (colorGenerator 2) g))-
    sourcePair f (chargeAction (colorGenerator 2) (A g))=0
  rw [paired,sourceColorCharge_pair,sourceColorCharge_pair,paired,commutes,sub_self]

theorem sourceColor_coframeDerivative (v : SourceCoordinateSlice) (f : QuantumTest) :
    GaussCoframeCore.derivative v (chargeAction (colorGenerator 2) f)=
      chargeAction (colorGenerator 2) (GaussCoframeCore.derivative v f) := by
  apply DFunLike.ext
  intro z
  change (TestFunction.lineDerivCLM (n:=⊤) (k:=⊤) ℂ v (chargeAction (colorGenerator 2) f)) z=
    sourceColorChargeFiber ((TestFunction.lineDerivCLM (n:=⊤) (k:=⊤) ℂ v f) z)
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp),TestFunction.lineDerivCLM_apply_of_le (by simp),
    (chargeAction (colorGenerator 2) f).contDiff.differentiable (by simp) |>.differentiableAt.lineDeriv_eq_fderiv,
    f.contDiff.differentiable (by simp) |>.differentiableAt.lineDeriv_eq_fderiv]
  have h:=(sourceColorChargeFiber.restrictScalars ℝ).hasFDerivAt.comp z
    (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change (fderiv ℝ ((sourceColorChargeFiber.restrictScalars ℝ) ∘ f) z) v=_
  rw [h.fderiv]
  rfl

theorem sourceColor_coframeMomentum (i : Fin 6) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeCore.momentum i) := by
  apply Commute.symm
  apply LinearMap.ext
  intro f
  change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (chargeAction (colorGenerator 2) f)=
    chargeAction (colorGenerator 2) ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f)
  rw [sourceColor_coframeDerivative,map_smul]

theorem sourceColor_coframeAdjoint (i : Fin 6) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeCore.adjoint i) := by
  apply Commute.symm
  apply LinearMap.ext
  exact colour_adjoint _ _ (GaussCoframeKinetic.adjoint_pair i)
    (fun f=>LinearMap.congr_fun (sourceColor_coframeMomentum i).symm.eq f)

theorem sourceColor_spin_full (a : Fin 7) :
    GaussCoframeSpin.full a*nativeFull (colorGenerator 2)=nativeFull (colorGenerator 2)*GaussCoframeSpin.full a := by
  have hp:=GaussMatterCore.spin_native_commute (GaussCoframeSpin.sourceSpin a) (colorGenerator 2)
  change GaussCoframeSpin.primal a*nativePrimal (colorGenerator 2)=nativePrimal (colorGenerator 2)*GaussCoframeSpin.primal a at hp
  have hd:=congrArg (fun M=>M.map (starRingEnd ℂ)) hp
  rw [Matrix.map_mul,Matrix.map_mul] at hd
  change Matrix.fromBlocks (GaussCoframeSpin.primal a) 0 0
      (if a.val<3 then (GaussCoframeSpin.primal a).map (starRingEnd ℂ) else -(GaussCoframeSpin.primal a).map (starRingEnd ℂ))*
      Matrix.fromBlocks (nativePrimal (colorGenerator 2)) 0 0 ((nativePrimal (colorGenerator 2)).map (starRingEnd ℂ))=_
  rw [Matrix.fromBlocks_multiply]
  change _=Matrix.fromBlocks (nativePrimal (colorGenerator 2)) 0 0 ((nativePrimal (colorGenerator 2)).map (starRingEnd ℂ))*
    Matrix.fromBlocks (GaussCoframeSpin.primal a) 0 0
      (if a.val<3 then (GaussCoframeSpin.primal a).map (starRingEnd ℂ) else -(GaussCoframeSpin.primal a).map (starRingEnd ℂ))
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
  rw [hp]
  by_cases ha : a.val<3
  · simp only [ha,if_true,hd]
  · simp only [ha,if_false,Matrix.neg_mul,Matrix.mul_neg,hd]

theorem sourceColor_spinCurrent (a : Fin 7) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeSpin.current a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (quantized (chargeMatrix (colorGenerator 2))*quantized (GaussCoframeSpin.full a)) (f z)=
    (quantized (GaussCoframeSpin.full a)*quantized (chargeMatrix (colorGenerator 2))) (f z)
  apply congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (f z))
  exact (CanonicalPhysicalForce.quantized_commute _ _ (by
    simp only [chargeMatrix,smul_mul_assoc,mul_smul_comm,sourceColor_spin_full])).eq


private theorem commute_smul {A : QuantumEnd} (h : Commute (chargeAction (colorGenerator 2)) A) (c : ℂ) :
    Commute (chargeAction (colorGenerator 2)) (c • A) := by
  show chargeAction (colorGenerator 2)*(c • A)=(c • A)*chargeAction (colorGenerator 2)
  rw [mul_smul_comm,smul_mul_assoc,h.eq]

theorem sourceColor_scalar (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (chargeAction (colorGenerator 2)) (GaussNativeForm.multiply c smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change sourceColorChargeFiber ((c z : ℂ) • f z)=(c z : ℂ) • sourceColorChargeFiber (f z)
  exact map_smul sourceColorChargeFiber (c z : ℂ) (f z)

private theorem compose_commutes (A B : QuantumEnd)
    (hA : Commute (chargeAction (colorGenerator 2)) A) (hB : Commute (chargeAction (colorGenerator 2)) B) :
    Commute (chargeAction (colorGenerator 2)) (A.comp B) := by
  apply LinearMap.ext
  intro f
  change chargeAction (colorGenerator 2) (A (B f))=A (B (chargeAction (colorGenerator 2) f))
  exact (show chargeAction (colorGenerator 2) (A (B f))=A (chargeAction (colorGenerator 2) (B f)) from LinearMap.congr_fun hA.eq (B f)).trans
    (congrArg A (show chargeAction (colorGenerator 2) (B f)=B (chargeAction (colorGenerator 2) f) from LinearMap.congr_fun hB.eq f))
private theorem add_commutes (A B : QuantumEnd)
    (hA : Commute (chargeAction (colorGenerator 2)) A) (hB : Commute (chargeAction (colorGenerator 2)) B) :
    Commute (chargeAction (colorGenerator 2)) (A+B) := by
  apply LinearMap.ext
  intro f
  change chargeAction (colorGenerator 2) (A f+B f)=A (chargeAction (colorGenerator 2) f)+B (chargeAction (colorGenerator 2) f)
  rw [map_add]
  exact congrArg₂ (fun x y : QuantumTest=>x+y) (LinearMap.congr_fun hA.eq f) (LinearMap.congr_fun hB.eq f)
private theorem sum_commutes {ι : Type*} [Fintype ι] (A : ι→QuantumEnd)
    (h : ∀ i,Commute (chargeAction (colorGenerator 2)) (A i)) :
    Commute (chargeAction (colorGenerator 2)) (∑ i,A i) := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact LinearMap.congr_fun (h i).eq f

theorem sourceColor_coframeTerm (i j : Fin 6) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeKinetic.term i j) :=
  compose_commutes _ _ (sourceColor_coframeAdjoint i) (compose_commutes _ _
    (sourceColor_scalar _ (GaussCoframeKinetic.coefficient_smooth i j)) (sourceColor_coframeMomentum j))

theorem sourceColor_coframeMixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeForm.mixed i a c smooth) :=
  commute_smul (add_commutes _ _
    (compose_commutes _ _ (sourceColor_spinCurrent a) (compose_commutes _ _ (sourceColor_scalar c smooth) (sourceColor_coframeMomentum i)))
    (compose_commutes _ _ (sourceColor_coframeAdjoint i) (compose_commutes _ _ (sourceColor_scalar c smooth) (sourceColor_spinCurrent a)))) _

theorem sourceColor_number : Commute (chargeAction (colorGenerator 2)) GaussCoframeForm.number := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have each (g : QuantumTest) : GaussCoframeForm.number g z=SourceQuantumFockGauge.fiberNumber (g z) := by
    apply PiLp.ext
    intro word
    rw [GaussCoframeForm.number_apply,SourceQuantumFockGauge.fiberNumber_apply]
  change sourceColorChargeFiber (GaussCoframeForm.number f z)=GaussCoframeForm.number (chargeAction (colorGenerator 2) f) z
  rw [each,each]
  change sourceColorChargeFiber (SourceQuantumFockGauge.fiberNumber (f z))=SourceQuantumFockGauge.fiberNumber (sourceColorChargeFiber (f z))
  exact congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (f z))
    (GaussQuantumMultiplier.number_commute (chargeMatrix (colorGenerator 2))).symm.eq

theorem sourceColor_coframeAction : Commute (chargeAction (colorGenerator 2)) GaussCoframeForm.coframeAction := by
  have kinetic : Commute (chargeAction (colorGenerator 2)) GaussCoframeKinetic.kinetic :=
    sum_commutes _ (fun i=>sum_commutes _ (fun j=>sourceColor_coframeTerm i j))
  have current : Commute (chargeAction (colorGenerator 2)) GaussCoframeForm.currentAction :=
    add_commutes _ _ (add_commutes _ _ (add_commutes _ _
      (sourceColor_coframeMixed _ _ _ (GaussCoframeForm.currentCoefficient_smooth 0))
      (sourceColor_coframeMixed _ _ _ (GaussCoframeForm.currentCoefficient_smooth 1)))
      (sourceColor_coframeMixed _ _ _ (fun z=>(GaussCoframeForm.currentCoefficient_smooth 0 z).neg)))
      (sourceColor_coframeMixed _ _ _ (GaussCoframeForm.currentCoefficient_smooth 2))
  have squares : Commute (chargeAction (colorGenerator 2)) (∑ a : Fin 7,GaussCoframeForm.spinSquare a) :=
    sum_commutes _ (fun a=>commute_smul (compose_commutes _ _ (sourceColor_spinCurrent a)
      (compose_commutes _ _ (sourceColor_scalar _ GaussCoframeForm.inverseVolume_smooth) (sourceColor_spinCurrent a))) _)
  have number : Commute (chargeAction (colorGenerator 2)) GaussCoframeForm.numberShift :=
    commute_smul (add_commutes _ _ (compose_commutes _ _ sourceColor_number (sourceColor_scalar _ GaussCoframeForm.numberCoefficient_smooth))
      (compose_commutes _ _ (sourceColor_scalar _ GaussCoframeForm.numberCoefficient_smooth) sourceColor_number)) _
  exact add_commutes _ _ (add_commutes _ _ (add_commutes _ _ (add_commutes _ _ kinetic current) squares) number)
    (sourceColor_scalar _ GaussCoframeForm.volumePotential_smooth)

def sourceMatterTorqueFiber (z : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber :=
  ∑ i : Fin 3,∑ b : Fin 3,
    (quantizer (GaussMatterCore.localMatrix i b z)*sourceColorChargeFiber-
      sourceColorChargeFiber*quantizer (GaussMatterCore.localMatrix i b z))

theorem sourceMatterTorque_generated (f : QuantumTest) (z : SourceCoordinateSlice) :
    sourceColorWardOperator GaussMatterCore.matterAction f z=sourceMatterTorqueFiber z (f z) := by
  change (∑ i : Fin 3,∑ b : Fin 3,quantizer (GaussMatterCore.localMatrix i b z) (sourceColorChargeFiber (f z)))-
    sourceColorChargeFiber (∑ i : Fin 3,∑ b : Fin 3,quantizer (GaussMatterCore.localMatrix i b z) (f z))=_
  simp only [map_sum,←Finset.sum_sub_distrib,sourceMatterTorqueFiber,sum_apply,sub_apply,mul_apply_eq_comp]

theorem sourceConfigurationTorque_generated :
    configurationTorque (colorGenerator 2)=sourceColorWardOperator GaussNativeForm.nativeAction+
      sourceColorWardOperator GaussMatterCore.matterAction := by
  change (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction).comp (chargeAction (colorGenerator 2))-
    (chargeAction (colorGenerator 2)).comp (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)=_
  have cf : GaussCoframeForm.coframeAction.comp (chargeAction (colorGenerator 2))=
      (chargeAction (colorGenerator 2)).comp GaussCoframeForm.coframeAction := sourceColor_coframeAction.symm.eq
  simp only [LinearMap.add_comp,LinearMap.comp_add,sourceColorWardOperator]
  rw [cf]
  abel

theorem sourceConfigurationTorque_ward (f g : QuantumTest) :
    sourcePair f (configurationTorque (colorGenerator 2) g)=sourceNativeTorque f g+
      sourcePair f (sourceColorWardOperator GaussMatterCore.matterAction g) := by
  rw [sourceConfigurationTorque_generated]
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
  change sourcePair f (sourceColorWardOperator GaussNativeForm.nativeAction g)+
    sourcePair f (sourceColorWardOperator GaussMatterCore.matterAction g)=_
  exact congrArg (fun e=>e+sourcePair f (sourceColorWardOperator GaussMatterCore.matterAction g)) (sourceNativeActionWard f g)


theorem sourceActualN1_gaussColorCore (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (k : PhysicalMomentum) (left : QuantumTest) :
    sourcePair left (sourceN1WardCore k (colorGenerator 2)
      (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))=
      sourceNativeTorque left (sourceTestApprox q.F (sourceActualN1Primal q p state z t))+
      sourcePair left (sourceColorWardOperator GaussMatterCore.matterAction
        (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))+
      sourcePair left (CanonicalPhysicalWardCore.currentAction k (colorGenerator 2)
        (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))+
      sourcePair left (yukawaTorque (colorGenerator 2)
        (sourceTestApprox q.F (sourceActualN1Primal q p state z t))) := by
  unfold sourceN1WardCore
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
  change sourcePair left (configurationTorque (colorGenerator 2) (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))+_+_=_
  rw [sourceConfigurationTorque_ward]
  rfl

end LowEnergy.PreparationVacuumPhysicalGaussColorTorque
