import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceVoltageNativeJet

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticVoltageSource
open SaturationMonoid.PhysicsCore
open Stage9C.Material.SpinPair PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumCausalPoleResponse
open PreparationVacuumCurrentNativeLaplaceBridge SourcePropagationNativeActionHessian
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open PreparationVacuumMixedFieldReturn PreparationCoordinates SourceQuantumNativeDimensions
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open StageNineP286ActionCauchySplit StageNineP286ActionVelocityLocalActualLift
open StageNineCanonicalCauchyState StageNineCoframeLocalDifferentiability
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open PreparationVacuumCurrentSignalRealization
open scoped Matrix BigOperators Topology ContDiff
attribute [local irreducible] originalJacobi sourceTemporalFirst sourceTemporalSecond

@[local simp] private theorem momentum_one (spatial : Fin 3→ℂ) (t : ℂ) : Fin.cases t spatial 1=spatial 0 := rfl
@[local simp] private theorem momentum_two (spatial : Fin 3→ℂ) (t : ℂ) : Fin.cases t spatial 2=spatial 1 := rfl
@[local simp] private theorem momentum_three (spatial : Fin 3→ℂ) (t : ℂ) : Fin.cases t spatial 3=spatial 2 := rfl

private def timeSliceTerms (time : ℤ) (terms : List SourceTerm) : List SourceTerm :=
  terms.map (fun a=>⟨a.row,a.column,⟨0,a.powers.first,a.powers.second,a.powers.third⟩,
    a.coefficient*(time:SourceCoefficient)^a.powers.temporal⟩)

private theorem timeSlice_value (time : ℤ) (terms : List SourceTerm) (spatial : Fin 3→ℂ) :
    sourceMatrix (timeSliceTerms time terms) (fullMomentum spatial 0)=
      sourceMatrix terms (fullMomentum spatial (time:ℂ)) := by
  induction terms with
  | nil=>rfl
  | cons a rest ih=>
    simp only [timeSliceTerms,List.map_cons,sourceMatrix_cons] at ih ⊢
    rw [ih]
    congr 1
    have coefficient : coefficientValue (a.coefficient*(time:SourceCoefficient)^a.powers.temporal)=
        coefficientValue a.coefficient*(time:ℂ)^a.powers.temporal := by
      change coefficientMap (a.coefficient*(time:SourceCoefficient)^a.powers.temporal)=_
      rw [map_mul,map_pow,map_intCast]
      rfl
    simp only [SourceTerm.matrix,coefficient]
    congr 1
    simp only [Powers.value,pow_zero,one_mul]
    change coefficientValue a.coefficient*(time:ℂ)^a.powers.temporal*
      ((spatial 0)^a.powers.first*(spatial 1)^a.powers.second*(spatial 2)^a.powers.third)=
      coefficientValue a.coefficient*((time:ℂ)^a.powers.temporal*(spatial 0)^a.powers.first*(spatial 1)^a.powers.second*(spatial 2)^a.powers.third)
    ring

/-- The source's complete voltage and constitutive gauge-B amplitudes in its original Fourier coordinates. -/
def sourceVoltageSpatialVector (spatial : Fin 3→ℂ) : Fin 289→ℂ :=
  Pi.single 20 1+Pi.single 264 (-(2*(lapse:ℂ))*spatial 0)+
    Pi.single 276 (-(2*(lapse:ℂ))*spatial 1)+Pi.single 288 (-(2*(lapse:ℂ))*spatial 2)

def sourceVoltageTemporalVector : Fin 289→ℂ := Pi.single 8 (-1)

/-- The time derivative coefficient is from the native action's proved temporal pencil. -/
theorem sourceVoltage_time_coefficient (spatial : Fin 3→ℂ) :
    sourceTemporalFirst spatial=(1/2:ℂ) •
      (originalJacobi (fullMomentum spatial 1)-originalJacobi (fullMomentum spatial (-1))) := by
  rw [sourceTemporalPencil_original spatial 1,sourceTemporalPencil_original spatial (-1)]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

def sourceVoltageWholeForcing (spatial : Fin 3→ℂ) : Fin 289→ℂ :=
  originalJacobi (fullMomentum spatial 0)*ᵥsourceVoltageSpatialVector spatial+
    sourceTemporalFirst spatial*ᵥsourceVoltageTemporalVector

private def voltageLiftTerms : List SourceTerm :=
  [⟨20,0,⟨0,0,0,0⟩,1⟩,
   ⟨264,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩,
   ⟨276,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩,
   ⟨288,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩]
private def timeLiftTerms : List SourceTerm := [⟨8,0,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩]
private def voltageWholeTerms : List SourceTerm :=
  productTerms (timeSliceTerms 0 originalJacobiTerms) voltageLiftTerms ++
    productTerms (timeSliceTerms 1 originalJacobiTerms ++ negativeTerms (timeSliceTerms (-1) originalJacobiTerms)) timeLiftTerms
private def voltageLiteralTerms : List SourceTerm :=
  [⟨20,0,⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩,
   ⟨20,0,⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩,
   ⟨20,0,⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,-6/25⟩⟩⟩,
   ⟨74,0,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
   ⟨76,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
   ⟨80,0,⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩⟩,
   ⟨82,0,⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩⟩,
   ⟨98,0,⟨0,0,0,0⟩,-1⟩,⟨100,0,⟨0,0,0,0⟩,1⟩,
   ⟨104,0,⟨0,0,0,0⟩,1⟩,⟨106,0,⟨0,0,0,0⟩,-1⟩]

private theorem voltage_terms_generated : fastNormalizeTerms (voltageWholeTerms++negativeTerms voltageLiteralTerms)=[] := by
  decide +kernel

private theorem lapse_coefficient : (6/25:ℂ)*rootTwo*rootFifteen=2*(lapse:ℂ) := by
  have two : (Real.sqrt 2)^2=2:=Real.sq_sqrt (by norm_num)
  have fifteen : (Real.sqrt 15)^2=15:=Real.sq_sqrt (by norm_num)
  have positive : 0≤(3/25:ℝ)*Real.sqrt 2*Real.sqrt 15 := by positivity
  have equal : (3/25:ℝ)*Real.sqrt 2*Real.sqrt 15=lapse := by
    nlinarith [lapse_sq,lapse_pos,mul_self_nonneg ((3/25:ℝ)*Real.sqrt 2*Real.sqrt 15-lapse)]
  unfold rootTwo rootFifteen
  have h := congrArg (fun x : ℝ => (x:ℂ)) equal
  push_cast at h
  linear_combination 2*h

def sourceVoltageMatterForcing : Fin 289→ℂ :=
  Pi.single 74 rootTwo-Pi.single 76 rootTwo-Pi.single 80 rootTwo+Pi.single 82 rootTwo-
    Pi.single 98 1+Pi.single 100 1+Pi.single 104 1-Pi.single 106 1

private theorem lift_coefficient : coefficientValue (⟨⟨0,0⟩,⟨0,-6/25⟩⟩:SourceCoefficient)=-(2*(lapse:ℂ)) := by
  norm_num [coefficientValue]
  linear_combination lapse_coefficient

private theorem voltageLift_value (spatial : Fin 3→ℂ) :
    sourceMatrix voltageLiftTerms (fullMomentum spatial 0)*ᵥPi.single 0 1=sourceVoltageSpatialVector spatial := by
  ext i
  norm_num [voltageLiftTerms,sourceMatrix,SourceTerm.matrix,Powers.value,fullMomentum,
    Matrix.add_mulVec,Matrix.single_mulVec,Matrix.mulVec_single,Matrix.col,Matrix.add_apply,Matrix.single_apply,Pi.single_apply,Matrix.single,eq_comm,lift_coefficient,coefficientValue,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,sourceVoltageSpatialVector]
  rw [←lapse_coefficient]
  split_ifs <;> try omega
  all_goals norm_num <;> ring

private theorem timeLift_value (spatial : Fin 3→ℂ) :
    sourceMatrix timeLiftTerms (fullMomentum spatial 0)*ᵥPi.single 0 1=(1/2:ℂ) • sourceVoltageTemporalVector := by
  ext i
  norm_num [timeLiftTerms,sourceMatrix,SourceTerm.matrix,Powers.value,fullMomentum,
    Matrix.single_mulVec,Matrix.mulVec_single,Matrix.col,Matrix.single_apply,Matrix.single,Pi.single_apply,eq_comm,coefficientValue,sourceVoltageTemporalVector]

private theorem literal_value (spatial : Fin 3→ℂ) :
    sourceMatrix voltageLiteralTerms (fullMomentum spatial 0)*ᵥPi.single 0 1=
      Pi.single 20 (-(2*(lapse:ℂ))*∑j : Fin 3,(spatial j)^2)+sourceVoltageMatterForcing := by
  ext i
  norm_num [voltageLiteralTerms,sourceMatrix,SourceTerm.matrix,Powers.value,fullMomentum,
    Matrix.add_mulVec,Matrix.single_mulVec,Matrix.mulVec_single,Matrix.col,Matrix.add_apply,Matrix.single_apply,Pi.single_apply,Matrix.single,eq_comm,lift_coefficient,coefficientValue,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,sourceVoltageMatterForcing]
  rw [←lapse_coefficient]
  simp only [Fin.sum_univ_three]
  split_ifs <;> try omega
  all_goals norm_num <;> ring

/-- The whole original source fold gives the Gauss row and every nonzero matter row together. -/
theorem sourceVoltageWholeForcing_generated (spatial : Fin 3→ℂ) :
    sourceVoltageWholeForcing spatial=
      Pi.single 20 (-(2*(lapse:ℂ))*∑j : Fin 3,(spatial j)^2)+sourceVoltageMatterForcing := by
  have generated := congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥPi.single 0 1)
    (normalization_equal voltageWholeTerms voltageLiteralTerms voltage_terms_generated (fullMomentum spatial 0))
  simp only [voltageWholeTerms,sourceMatrix_append,productTerms_value,negativeTerms_value,
    timeSlice_value,Matrix.add_mulVec,←Matrix.mulVec_mulVec,voltageLift_value,timeLift_value,literal_value] at generated
  rw [sourceVoltageWholeForcing,sourceVoltage_time_coefficient]
  convert generated using 1
  simp only [originalJacobi,sub_eq_add_neg,Matrix.mulVec_smul,Matrix.smul_mulVec,Matrix.add_mulVec,smul_add,Int.cast_zero,Int.cast_one,Int.cast_neg]

theorem sourceVoltageWholeForcing_gauss (spatial : Fin 3→ℂ) :
    sourceVoltageWholeForcing spatial 20=-(2*(lapse:ℂ))*∑j : Fin 3,(spatial j)^2 := by
  rw [sourceVoltageWholeForcing_generated]
  norm_num [sourceVoltageMatterForcing,Pi.single_apply,Fin.ext_iff]

/-- Original physical Fourier momenta give the positive inverse-Laplacian price in the same time coordinate. -/
theorem sourceVoltageWholeForcing_physical (n : PhysicalMomentum) :
    sourceVoltageWholeForcing (physicalSpatial n) 20=2*(lapse:ℂ)*(spatialSquare n:ℂ) := by
  rw [sourceVoltageWholeForcing_gauss]
  simp only [physicalSpatial,spatialSquare,Fin.sum_univ_three,Complex.ofReal_add,Complex.ofReal_pow]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The voltage family has a genuine complete matter response; its other equations are not erased by the Gauss read. -/
theorem sourceVoltageMatterForcing_nonzero : sourceVoltageMatterForcing≠0 := by
  intro zero
  have component:=congrFun zero 74
  norm_num [sourceVoltageMatterForcing,rootTwo,Pi.single_apply,Fin.ext_iff] at component

/-- A genuine spacetime signal with the original scalar normal-time factor. -/
def sourceVoltageRamp (p : Fin 4→ℂ) (u v : Fin 289→ℂ) (x : BasePoint) : Field289 :=
  fun i=>(Complex.exp (sourcePhase p x)*(u i+(x 0:ℂ)*v i)).re

private def rampStep (p : Fin 4→ℂ) (u v : Fin 289→ℂ) (mu : Fin 4) : Fin 289→ℂ :=
  fun i=>p mu*u i+(if mu=0 then v i else 0)

private theorem ramp_smooth (p : Fin 4→ℂ) (u v : Fin 289→ℂ) : ContDiff ℝ ∞ (sourceVoltageRamp p u v) := by
  apply contDiff_pi.mpr
  intro i
  exact Complex.reCLM.contDiff.comp (((sourcePhase p).contDiff.cexp).mul
    (contDiff_const.add ((Complex.ofRealCLM.contDiff.comp (PiLp.proj 2 (fun _ : Fin 4=>ℝ) 0).contDiff).mul contDiff_const)))

private theorem ramp_derivative (p : Fin 4→ℂ) (u v : Fin 289→ℂ) (x : BasePoint) (mu : Fin 4) :
    fieldDirectionalDerivative (sourceVoltageRamp p u v) x mu=
      sourceVoltageRamp p (rampStep p u v mu) (fun i=>p mu*v i) x := by
  have d (i : Fin 289) := Complex.reCLM.hasFDerivAt.comp x
    (((sourcePhase p).hasFDerivAt.cexp).mul
      (((Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 4=>ℝ) 0)).hasFDerivAt.mul_const (v i)).const_add (u i)))
  have whole := hasFDerivAt_pi.mpr d
  change HasFDerivAt (sourceVoltageRamp p u v) _ x at whole
  have axis (j : Fin 4) : sourcePhase p (EuclideanSpace.single j 1)=p j := sourcePhase_coordinate p j
  rw [fieldDirectionalDerivative,whole.fderiv]
  funext i
  simp only [ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,add_apply,
    smul_apply,Complex.reCLM_apply,sourcePhase_coordinate,Complex.ofRealCLM_apply,PiLp.proj_apply,
    coordinateDirection,axis,PiLp.single_apply,sourceVoltageRamp,rampStep,smul_eq_mul]
  fin_cases mu <;> norm_num [axis,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im] <;> ring

private theorem ramp_first (p : Fin 4→ℂ) (u v : Fin 289→ℂ) :
    signalFirstJet (sourceVoltageRamp p u v)=fun x=>
      (sourceVoltageRamp p u v x,fun mu=>sourceVoltageRamp p (rampStep p u v mu) (fun i=>p mu*v i) x) := by
  funext x
  simp only [signalFirstJet,ramp_derivative]

private theorem ramp_second (p : Fin 4→ℂ) (u v : Fin 289→ℂ) :
    signalSecondJet (sourceVoltageRamp p u v) 0=
      ((fun i=>(u i).re,fun mu i=>(rampStep p u v mu i).re),
       fun mu=>(fun i=>(rampStep p u v mu i).re,
         fun nu i=>(rampStep p (rampStep p u v nu) (fun j=>p nu*v j) mu i).re)) := by
  have zero (a b : Fin 289→ℂ) : sourceVoltageRamp p a b 0=fun i=>(a i).re := by
    funext i
    change (Complex.exp (sourcePhase p 0)*(a i+(0:ℂ)*b i)).re=(a i).re
    rw [map_zero,Complex.exp_zero,zero_mul,add_zero,one_mul]
  apply Prod.ext
  · change signalFirstJet (sourceVoltageRamp p u v) 0=_
    rw [ramp_first]
    simp only [zero]
  · funext mu
    change fieldDirectionalDerivative (signalFirstJet (sourceVoltageRamp p u v)) 0 mu=_
    rw [ramp_first]
    have first := (ramp_smooth p u v).differentiable (by simp) |>.differentiableAt (x:=0)
    have other (nu : Fin 4) := (ramp_smooth p (rampStep p u v nu) (fun i=>p nu*v i)).differentiable (by simp) |>.differentiableAt (x:=0)
    have all := first.hasFDerivAt.prodMk (hasFDerivAt_pi.mpr (fun nu=>(other nu).hasFDerivAt))
    rw [fieldDirectionalDerivative,all.fderiv]
    apply Prod.ext
    · change fieldDirectionalDerivative (sourceVoltageRamp p u v) 0 mu=_
      rw [ramp_derivative,zero]
    · funext nu
      change fieldDirectionalDerivative (sourceVoltageRamp p (rampStep p u v nu) (fun i=>p nu*v i)) 0 mu=_
      rw [ramp_derivative,zero]

/-- The temporal coefficient is the jet of actual coordinate time, generated by differentiating the curve. -/
theorem sourceVoltage_timeJet (spatial : Fin 3→ℂ) (u v : Fin 289→ℂ) :
    signalSecondJet (sourceVoltageRamp (fullMomentum spatial 0) u v) 0=
      sourceRealSecondJet (fullMomentum spatial 0) u+
        (1/2:ℝ) • (sourceRealSecondJet (fullMomentum spatial 1) v-
          sourceRealSecondJet (fullMomentum spatial (-1)) v) := by
  rw [ramp_second]
  apply Prod.ext
  · apply Prod.ext
    · funext i
      simp [sourceRealSecondJet,sourceRealFirstJet]
    · funext mu i
      fin_cases mu <;> simp [rampStep,sourceRealSecondJet,sourceRealFirstJet,fullMomentum,Complex.mul_re,Complex.mul_im] <;> ring
  · funext mu
    apply Prod.ext
    · funext i
      fin_cases mu <;> simp [rampStep,sourceRealSecondJet,sourceRealFirstJet,fullMomentum,Complex.mul_re,Complex.mul_im] <;> ring
    · funext nu i
      fin_cases mu <;> fin_cases nu <;> simp [rampStep,sourceRealSecondJet,sourceRealFirstJet,fullMomentum,Complex.mul_re,Complex.mul_im] <;> ring

/-- Fourier profiles use the very same derivative coordinates as the original source symbol. -/
def sourceVoltageFourierProfile (spatial : Fin 3→ℂ) (a : ℂ) (x : BasePoint) : ℝ :=
  (Complex.exp (sourcePhase (fullMomentum spatial 0) x)*a).re

private theorem profile_derivative (spatial : Fin 3→ℂ) (a : ℂ) (x : BasePoint) (mu : Fin 4) :
    fieldDirectionalDerivative (sourceVoltageFourierProfile spatial a) x mu=
      (Complex.exp (sourcePhase (fullMomentum spatial 0) x)*fullMomentum spatial 0 mu*a).re := by
  have d := Complex.reCLM.hasFDerivAt.comp x
    (((sourcePhase (fullMomentum spatial 0)).hasFDerivAt.cexp).mul_const a)
  change HasFDerivAt (sourceVoltageFourierProfile spatial a) _ x at d
  rw [fieldDirectionalDerivative,d.fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,Complex.reCLM_apply,
    sourcePhase_coordinate,smul_eq_mul]
  congr 1
  ring

private theorem profile_slice (spatial : Fin 3→ℂ) (a : ℂ) (x : BasePoint) :
    sourceVoltageFourierProfile spatial a (canonicalCauchySlicePoint 0 (canonicalSpatialProjection x))=
      sourceVoltageFourierProfile spatial a x := by
  unfold sourceVoltageFourierProfile
  congr 3
  simp [sourcePhase_apply,fullMomentum,Fin.sum_univ_four,canonicalCauchySlicePoint,
    canonicalSpatialProjection,canonicalLorentzianTimeDirection,
    localBaseCoordinate_apply,Fin.sum_univ_three]

/-- The original normal scalar and constitutive B family equals this actual Fourier/time curve in all 289 coordinates. -/
theorem sourceVoltage_signal_fourier (spatial : Fin 3→ℂ) (a : ℂ) :
    sourceVoltageSignal (sourceVoltageFourierProfile spatial a) 1=
      sourceVoltageRamp (fullMomentum spatial 0)
        (fun i=>a*sourceVoltageSpatialVector spatial i) (fun i=>a*sourceVoltageTemporalVector i) := by
  funext x i
  simp only [sourceVoltageSignal,one_mul,profile_slice,profile_derivative,
    sourceVoltageCoordinates,sourceVoltageSpatialVector,sourceVoltageTemporalVector,
    sourceVoltageRamp,Pi.add_apply,Pi.single_apply]
  split_ifs <;> try omega
  all_goals simp [sourceVoltageFourierProfile,canonicalTimeProjection,localBaseCoordinate_apply,
    canonicalLorentzianTimeDirection,fullMomentum,
    Complex.mul_re,Complex.mul_im] <;> ring

private theorem euler_combination (j k l : NativeSecondJet) (i : Fin 289) :
    nativeEulerLinearJet (j+(1/2:ℝ) • (k-l)) i=
      nativeEulerLinearJet j i+(1/2:ℝ)*(nativeEulerLinearJet k i-nativeEulerLinearJet l i) := by
  change nativeHessian (j.1+(1/2:ℝ) • (k.1-l.1)) (nativeJetBasis (none,i))-
    (∑mu : Fin 4,nativeHessian (j.2 mu+(1/2:ℝ) • (k.2 mu-l.2 mu)) (nativeJetBasis (some mu,i)))=_
  simp only [nativeEulerLinearJet,Prod.fst_add,Prod.snd_add,Prod.fst_smul,Prod.snd_smul,
    Prod.fst_sub,Prod.snd_sub,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,map_add,map_smul,map_sub,
    add_apply,smul_apply,sub_apply,
    smul_eq_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,Fin.sum_univ_four]
  ring

/-- The original Euler derivative of the actual normal/constitutive family generates the entire source column. -/
theorem sourceVoltage_Euler_fourier (spatial : Fin 3→ℂ) (a : ℂ) (i : Fin 289) :
    HasDerivAt (fun amplitude : ℝ=>nativeHolonomicEuler
      (sourceVoltageSignal (sourceVoltageFourierProfile spatial a) amplitude) 0 i)
      (a*sourceVoltageWholeForcing spatial i).re 0 := by
  have smooth : ContDiff ℝ ∞ (sourceVoltageFourierProfile spatial a) :=
    Complex.reCLM.contDiff.comp (((sourcePhase (fullMomentum spatial 0)).contDiff.cexp).mul contDiff_const)
  have generated := sourceVoltage_Euler_generated (sourceVoltageFourierProfile spatial a) smooth 0 i
  rw [sourceVoltage_signal_fourier,sourceVoltage_timeJet,euler_combination,
    sourceRealEuler_Fourier,sourceRealEuler_Fourier,sourceRealEuler_Fourier,
    nativeActionFourierHessian_original,nativeActionFourierHessian_original,nativeActionFourierHessian_original] at generated
  convert generated using 1
  rw [sourceVoltageWholeForcing,sourceVoltage_time_coefficient]
  simp only [Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  have commute (m : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 289→ℂ) :
      (m*ᵥfun j=>a*v j) i=a*(m*ᵥv) i := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [commute,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im]
  norm_num
  ring

theorem sourceVoltage_Euler_all_rows (spatial : Fin 3→ℂ) (a : ℂ) (i : Fin 289) :
    HasDerivAt (fun amplitude : ℝ=>nativeHolonomicEuler
      (sourceVoltageSignal (sourceVoltageFourierProfile spatial a) amplitude) 0 i)
      (a*(((Pi.single 20 (-(2*(lapse:ℂ))*(∑j : Fin 3,(spatial j)^2)) : Fin 289→ℂ)+sourceVoltageMatterForcing) i)).re 0 := by
  simpa only [sourceVoltageWholeForcing_generated] using sourceVoltage_Euler_fourier spatial a i

/-- The Gauss price is the amplitude derivative of the same complete voltage-family Euler. -/
theorem sourceVoltage_Euler_gauss (n : PhysicalMomentum) (a : ℂ) :
    HasDerivAt (fun amplitude : ℝ=>nativeHolonomicEuler
      (sourceVoltageSignal (sourceVoltageFourierProfile (physicalSpatial n) a) amplitude) 0 20)
      (2*lapse*spatialSquare n*a.re) 0 := by
  have generated:=sourceVoltage_Euler_fourier (physicalSpatial n) a 20
  rw [sourceVoltageWholeForcing_physical] at generated
  convert generated using 1 <;>
    simp [Complex.mul_re,Complex.mul_im] <;> ring

/-- The frequency convention is read from the actual source phase, including its 2π and I. -/
theorem sourceVoltage_frequency_phase (frequency : PhysicalMomentum) (x : BasePoint) :
    sourcePhase (fullMomentum (physicalSpatial (fun j=>2*Real.pi*frequency j)) 0) x=
      (2*Real.pi:ℂ)*Complex.I*(∑j : Fin 3,(frequency j:ℂ)*(x j.succ:ℂ)) := by
  simp [sourcePhase_apply,fullMomentum,physicalSpatial,Fin.sum_univ_four,Fin.sum_univ_three]
  ring

end LowEnergy.PreparationVacuumStaticVoltageSource
