import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFullPoleTensor
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceConstraintBoundary

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPoleConstraintReturn
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumFullPoleContinuation
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalConstraint114 PreparationVacuumPhysicalZeroRead
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumFieldConstraintResponse
open Filter MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.Operator

private theorem external_field_return (A : Matrix (Fin 289) (Fin 289) ℂ)
    (U V : Matrix RestStateIndex RestStateIndex ℂ) (J : RestStateIndex→RestStateIndex→Fin 289→ℂ)
    (l r : RestStateIndex) (i : Fin 289) :
    (A*ᵥ(fun j=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>J a b j)*V) l r)) i=
      (U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>(A*ᵥJ a b) i)*V) l r:=by
  simp only [Matrix.mul_apply,Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

def axisCosource (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) (κ : staticDomain) : Fin 289→ℂ:=
  originalReadback (staticMomentum κ.val)*ᵥactualAxisWindow q l r T κ

def axisNullCosource (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) (κ : staticDomain) : Fin 289→ℂ:=
  nullProjection*ᵥaxisCosource q l r T κ

theorem axisCosource_actual (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (κ : staticDomain) (i : Fin 289) :
    axisCosource q l r T κ i=
      (movingOverlap (sourceAxisLeft 0 κ.val)*
        (show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>actualCosource q (sourceAxisLeft 0 κ.val) 0 a b 0 T i)*
        (movingOverlap 0).conjTranspose) l r:=by
  have each (a b : RestStateIndex) :
      originalReadback (staticMomentum κ.val)*ᵥactualCurrent q (sourceAxisLeft 0 κ.val) 0 a b 0 T=
        actualCosource q (sourceAxisLeft 0 κ.val) 0 a b 0 T:=by
    simpa only [actual_static_momentum] using actual_current_ward q (sourceAxisLeft 0 κ.val) 0 a b 0 T
  have returned : returnedCurrentWindow q (sourceAxisLeft 0 κ.val) 0 l r 0 T=
      fun j=>(movingOverlap (sourceAxisLeft 0 κ.val)*
        (show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>actualCurrent q (sourceAxisLeft 0 κ.val) 0 a b 0 T j)*
        (movingOverlap 0).conjTranspose) l r:=by
    funext j
    exact returnedCurrentWindow_tensor q (sourceAxisLeft 0 κ.val) 0 l r 0 T j
  unfold axisCosource actualAxisWindow
  rw [returned]
  exact (external_field_return _ _ _ (fun a b=>actualCurrent q (sourceAxisLeft 0 κ.val) 0 a b 0 T) l r i).trans
    (by simp only [each])

private theorem sourceMatrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms):=by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix:=by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

private theorem readback_continuous : Continuous originalReadback:=by
  unfold originalReadback originalChange
  exact ((sourceMatrix_continuous originalChangeTerms).comp continuous_neg).matrix_transpose

theorem axisCosource_tendsto (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (axisCosource q l r T) staticApproach (𝓝 (actualCosource q 0 0 l r 0 T)):=by
  have readback:=readback_continuous.continuousAt.tendsto.comp staticMomentum_tendsto
  have h:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (readback.prodMk_nhds (actualAxisWindow_tendsto q l r T nonrealL nonrealR))
  have origin : actualMomentum 0 0 0=0:=by
    have left : sourceAxisLeft (0:PhysicalMomentum) 0=0:=by
      ext i
      fin_cases i <;> norm_num [sourceAxisLeft,sourceAxisTransfer]
    have field : staticMomentum 0=0:=by ext i;fin_cases i <;> simp [staticMomentum]
    simpa only [left,field] using actual_static_momentum (0:PhysicalMomentum) 0
  have law:=actual_current_ward q 0 0 l r 0 T
  rw [origin] at law
  unfold axisCosource
  simpa only [Function.comp_def,law] using h

theorem axisNullCosource_tendsto (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (axisNullCosource q l r T) staticApproach (𝓝 (nullProjection*ᵥactualCosource q 0 0 l r 0 T)):=
  (continuous_const.matrix_mulVec continuous_id).continuousAt.tendsto.comp
    (axisCosource_tendsto q l r T nonrealL nonrealR)

/-- The actual held-current pole weight is the negative origin colour constraint source. -/
theorem actualOriginWeight_cosource114 (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) :
    actualOriginWeight q 0 0 l r 0 T= -(actualCosource q 0 0 l r 0 T 114):=by
  have spatial : PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalTransfer 0 0)=0:=by
    funext i
    simp [PreparationVacuumPhysicalFeedback.physicalSpatial,sourcePhysicalTransfer]
  unfold actualCosource
  rw [spatial,sourceActualCosource114_generated]
  unfold actualOriginWeight actualCurrent constraintCovariantRead
  simp only [Pi.zero_apply,zero_mul,zero_add,zero_div]
  ring

theorem actualAxisField_constraint_residue (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • actualAxisField q l r T κ) staticApproach
      (𝓝 (fullNativeOrigin*ᵥ
        (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*(-actualCosource q 0 0 l r 0 T 114))+
         Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*(-actualCosource q 0 0 l r 0 T 114))))):=by
  simpa only [actualOriginWeight_cosource114] using actualAxisField_coupled_residue q l r T nonrealL nonrealR

theorem actualAxisField_compatibility (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) (κ : staticDomain) :
    originalJacobi (staticMomentum κ.val)*ᵥactualAxisField q l r T κ=actualAxisWindow q l r T κ ↔
      axisNullCosource q l r T κ=0:=by
  have source:=actualAxisField_whole q l r T κ
  change originalJacobi (staticMomentum κ.val)*ᵥactualAxisField q l r T κ=
    actualAxisWindow q l r T κ-originalRowLift (staticMomentum κ.val)*ᵥaxisNullCosource q l r T κ at source
  constructor
  · intro compatible
    rw [compatible] at source
    have lifted : originalRowLift (staticMomentum κ.val)*ᵥaxisNullCosource q l r T κ=0:=by
      exact (sub_eq_self.mp source.symm)
    have inverse : originalReadback (staticMomentum κ.val)*originalRowLift (staticMomentum κ.val)=1:=by
      have h:=congrArg Matrix.transpose (original_inverse_change (-(staticMomentum κ.val)))
      simpa only [Matrix.transpose_mul,Matrix.transpose_one,originalReadback,originalRowLift] using h
    have read:=congrArg (fun v : Fin 289→ℂ=>originalReadback (staticMomentum κ.val)*ᵥv) lifted
    simpa only [Matrix.mulVec_mulVec,inverse,Matrix.one_mulVec,Matrix.mulVec_zero] using read
  · intro compatible
    simpa only [compatible,Matrix.mulVec_zero,sub_zero] using source

end LowEnergy.PreparationVacuumPoleConstraintReturn
