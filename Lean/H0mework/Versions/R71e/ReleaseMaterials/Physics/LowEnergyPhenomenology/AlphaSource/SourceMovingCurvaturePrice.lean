import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCurvatureFrechet

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCurvatureSheetLimit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumFullSlowFieldResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumFieldConstraintResponse
open PreparationPhysicalFinitePoleCurvatureReturn PreparationPhysicalNormalizedFullField
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor CanonicalGradedSpatialSource
open Filter Set Asymptotics
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.Operator
attribute [local irreducible] sourceNativeFrame fullKernelFrame fullInverse sourceChargedNativeFrameJet

private theorem momentum_continuous (n : PhysicalMomentum) :
    Continuous (fun s : ℝ=>physicalFrequencyMomentum s n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun _=>continuous_const) i
  change Continuous (fun s : ℝ=>-Complex.I*(s:ℂ))
  fun_prop

/-- The moving direction converges by the original generated physical sheet. -/
theorem sourceCurvatureDirection_tendsto (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>physicalFrequencyMomentum (sourceSheet branch n unit e.val) n)
      scaleApproach (𝓝 (physicalFrequencyMomentum (sourceSpeed branch) n)) :=
  (momentum_continuous n).continuousAt.tendsto.comp ((sourceSheet_tendsto branch n unit).comp scaleVal_tendsto)

private theorem ray_real (e s : ℝ) (n : PhysicalMomentum) :
    frequencyRay e s n=(e^2:ℝ) • physicalFrequencyMomentum s n := by
  rw [frequencyRay_scaled]
  funext i
  simp only [Pi.smul_apply,Complex.real_smul,Complex.ofReal_pow,smul_eq_mul]

private theorem moving_remainder (f : (Fin 4→ℂ)→ℂ) (differentiable : DifferentiableAt ℝ f 0)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>
      (f (frequencyRay e.val (sourceSheet branch n unit e.val) n)-f 0-
        (e.val:ℂ)^2*(fderiv ℝ f 0) (physicalFrequencyMomentum (sourceSheet branch n unit e.val) n))/(e.val:ℂ)^2)
      scaleApproach (𝓝 0) := by
  have little := (hasFDerivAt_iff_isLittleO_nhds_zero.mp differentiable.hasFDerivAt).comp_tendsto
    (sourceRay_soft_limit branch n unit)
  have direction : (fun e : scaleDomain=>physicalFrequencyMomentum (sourceSheet branch n unit e.val) n)
      =O[scaleApproach] (fun _=>(1:ℝ)) :=
    isBigO_const_of_tendsto (sourceCurvatureDirection_tendsto branch n unit) one_ne_zero
  have product := (isBigO_refl (fun e : scaleDomain=>e.val^2) scaleApproach).smul direction
  have rayPrice : (fun e : scaleDomain=>frequencyRay e.val (sourceSheet branch n unit e.val) n)
      =O[scaleApproach] (fun e : scaleDomain=>e.val^2) := by
    simpa only [ray_real,smul_eq_mul,mul_one] using product
  have priced:=little.trans_isBigO rayPrice
  have quotient:=priced.norm_left.tendsto_div_nhds_zero
  have linear (e : scaleDomain) :
      (fderiv ℝ f 0) (frequencyRay e.val (sourceSheet branch n unit e.val) n)=
        (e.val:ℂ)^2*(fderiv ℝ f 0) (physicalFrequencyMomentum (sourceSheet branch n unit e.val) n) := by
    rw [ray_real,map_smul]
    simp only [Complex.real_smul,Complex.ofReal_pow]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_apply,zero_add,linear,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs] using quotient

private def frameEntry (i j : Fin 289) : (Matrix (Fin 289) (Fin 289) ℂ)→L[ℝ]ℂ :=
  ({ toFun:=fun A=>A i j
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl } : (Matrix (Fin 289) (Fin 289) ℂ)→ₗ[ℝ]ℂ).toContinuousLinearMap

private theorem frame_entry_smooth (i j : Fin 289) :
    ContDiffAt ℝ ∞ (fun p=>sourceNativeFrame p i j) (0:Fin 4→ℂ) :=
  (frameEntry i j).contDiff.contDiffAt.comp 0 sourceNativeFrame_smooth

private theorem frame_frechet (v : Fin 4→ℂ) (i j : Fin 289) :
    (fderiv ℝ (fun p=>sourceNativeFrame p i j) 0) v=sourceChargedNativeFrameJet v i j := by
  have ray : HasDerivAt (fun d : ℝ=>(d:ℂ) • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).ofReal_comp.smul_const v
  have left:=((frame_entry_smooth i j).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0:ℝ) ray (show (0:Fin 4→ℂ)=(0:ℂ) • v by simp)
  have right:= (frameEntry i j).hasFDerivAt.comp_hasDerivAt (0:ℝ) (sourceChargedNativeFrame_derivative v)
  exact left.unique right

/-- The original full289 residual is priced on the moving actual sheet, rather than at a frozen direction. -/
theorem sourceNativeFrameResidual_sheet (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (i j : Fin 289) :
    Tendsto (fun e : scaleDomain=>
      sourceChargedNativeFrameResidual ((e.val:ℂ)^2) (physicalFrequencyMomentum (sourceSheet branch n unit e.val) n) i j/
        (e.val:ℂ)^2) scaleApproach (𝓝 0) := by
  have generated:=moving_remainder (fun p=>sourceNativeFrame p i j)
    ((frame_entry_smooth i j).differentiableAt (by simp)) branch n unit
  apply generated.congr'
  filter_upwards [] with e
  rw [frame_frechet,sourceChargedNativeFrame_origin,frequencyRay_scaled]
  have original:=congrFun (congrFun (sourceChargedNativeFrame_first_return ((e.val:ℂ)^2)
    (physicalFrequencyMomentum (sourceSheet branch n unit e.val) n)) i) j
  change sourceNativeFrame _ i j-(fullNativeOrigin*slowFastFrame) i j-
    (e.val:ℂ)^2*sourceChargedNativeFrameJet _ i j=sourceChargedNativeFrameResidual _ _ i j at original
  rw [original]

/-- The complete source curvature has its actual moving-ray remainder, with all seven derivative entries kept. -/
theorem sourceCurvatureFrame_sheet (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (r : Fin 36) (c : Fin 289) :
    Tendsto (fun e : scaleDomain=>
      (sourceCurvatureFrame (frequencyRay e.val (sourceSheet branch n unit e.val) n) r c-
        (e.val:ℂ)^2*sourceMatrix (sourceSlowCurvatureTerms++sourceFastCurvatureTerms)
          (physicalFrequencyMomentum (sourceSheet branch n unit e.val) n) (Fin.castLE (by decide) r) c)/(e.val:ℂ)^2)
      scaleApproach (𝓝 0) := by
  have generated:=moving_remainder (fun p=>sourceCurvatureFrame p r c)
    ((sourceCurvatureFrame_smooth r c).differentiableAt (by simp)) branch n unit
  simpa only [sourceCurvatureFrame_frechet,sourceCurvatureFrame_origin,sub_zero] using generated

end LowEnergy.PreparationPhysicalCurvatureSheetLimit
