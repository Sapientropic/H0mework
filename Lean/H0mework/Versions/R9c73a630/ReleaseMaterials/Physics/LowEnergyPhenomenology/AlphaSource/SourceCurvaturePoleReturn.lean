import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceMovingCurvaturePrice

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCurvatureSheetLimit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin
open PreparationVacuumMixedControl PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumFullSlowFieldResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumFieldConstraintResponse
open PreparationPhysicalFinitePoleCurvatureReturn PreparationPhysicalNormalizedFullField
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor CanonicalGradedSpatialSource
open Filter Set
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
attribute [local irreducible] sourceNativeFrame fullKernelFrame fullInverse sourceChargedNativeFrameJet
  sourceNativeFrequencyPolarization sourcePoleCoordinates

private theorem sourceMatrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have scalar : Continuous (fun p : Fin 4→ℂ=>coefficientValue a.coefficient*a.powers.value p) := by
      unfold Powers.value
      fun_prop
    have term : Continuous a.matrix := by
      have result:=scalar.smul (continuous_const : Continuous (fun _ : Fin 4→ℂ=>Matrix.single a.row a.column (1:ℂ)))
      change Continuous (fun p : Fin 4→ℂ=>(coefficientValue a.coefficient*a.powers.value p) • Matrix.single a.row a.column (1:ℂ)) at result
      change Continuous (fun p : Fin 4→ℂ=>Matrix.single a.row a.column (coefficientValue a.coefficient*a.powers.value p))
      simpa only [Matrix.smul_single,smul_eq_mul,mul_one] using result
    exact term.add ih

private theorem five_smul (z : ℂ) (v : Fin 5→ℂ) : fiveVector (z • v)=z • fiveVector v := by
  funext i
  simp only [fiveVector,Pi.smul_apply]
  split_ifs <;> simp

private theorem scaling_continuous : Continuous regularScaling := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold regularScaling
  simp only [Matrix.diagonal_apply]
  split_ifs <;> fun_prop

private theorem five_continuous : Continuous fiveVector := by
  apply continuous_pi
  intro i
  unfold fiveVector
  split_ifs <;> fun_prop

private theorem mulVec_limit {X : Type*} {m n : ℕ} {L : Filter X}
    {A : X→Matrix (Fin m) (Fin n) ℂ} {v : X→Fin n→ℂ}
    {B : Matrix (Fin m) (Fin n) ℂ} {w : Fin n→ℂ}
    (matrix : Tendsto A L (𝓝 B)) (vector : Tendsto v L (𝓝 w)) :
    Tendsto (fun x=>A x*ᵥv x) L (𝓝 (B*ᵥw)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  change Tendsto (fun x=>∑j : Fin n,A x i j*v x j) L (𝓝 (∑j : Fin n,B i j*w j))
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp matrix i) j)).mul (tendsto_pi_nhds.mp vector j)

/-- The original frequency-derivative residue normalization is retained on the actual five coordinates. -/
theorem sourcePoleCoordinates_normalized (branch : Fin 2) (epsilon sigma : ℝ) (n : PhysicalMomentum) :
    (2*(sigma:ℂ)) • sourcePoleCoordinates branch epsilon sigma n=
      fiveVector (regularScaling epsilon*ᵥ(((2*(sigma:ℂ)) • sourceResidue epsilon sigma n)*ᵥ
        Pi.single (residueIndex branch) (1:ℂ))) := by
  rw [Matrix.smul_mulVec,Matrix.mulVec_smul,five_smul,Matrix.mulVec_single_one]
  unfold sourcePoleCoordinates sourceNativePoleColumn
  rfl

/-- No fast direction is declared zero: its actual epsilon scaling is consumed before the cofactor limit. -/
theorem sourcePoleCoordinates_sheet (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ)) •
      sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n)
      scaleApproach (𝓝 (fiveVector (regularScaling 0*ᵥ
        (Matrix.single (residueIndex branch) (residueIndex branch) (softCoefficient branch:ℂ)*ᵥ
          Pi.single (residueIndex branch) (1:ℂ))))) := by
  have column:=mulVec_limit (sourceResidue_normalized_soft_limit branch n unit)
    (tendsto_const_nhds (x:=Pi.single (residueIndex branch) (1:ℂ)))
  have result:=mulVec_limit (scaling_continuous.continuousAt.tendsto.comp scaleVal_tendsto) column
  have five:=five_continuous.continuousAt.tendsto.comp result
  simpa only [sourcePoleCoordinates_normalized,Function.comp_def] using five

/-- The complete moving curvature matrix divided by the physical epsilon squared has its generated seven-term limit. -/
theorem sourceCurvatureFrame_divided (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (r : Fin 36) (c : Fin 289) :
    Tendsto (fun e : scaleDomain=>sourceCurvatureFrame (frequencyRay e.val (sourceSheet branch n unit e.val) n) r c/(e.val:ℂ)^2)
      scaleApproach (𝓝 (sourceMatrix (sourceSlowCurvatureTerms++sourceFastCurvatureTerms)
        (physicalFrequencyMomentum (sourceSpeed branch) n) (Fin.castLE (by decide) r) c)) := by
  have matrix:=(sourceMatrix_continuous (sourceSlowCurvatureTerms++sourceFastCurvatureTerms)).continuousAt.tendsto.comp
    (sourceCurvatureDirection_tendsto branch n unit)
  have entry:=tendsto_pi_nhds.mp (tendsto_pi_nhds.mp matrix (Fin.castLE (by decide) r)) c
  have combined:=(sourceCurvatureFrame_sheet branch n unit r c).add entry
  simp only [zero_add] at combined
  apply combined.congr'
  filter_upwards [] with e
  have nonzero : (e.val:ℂ)^2≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr e.property.1.ne')
  simp only [Function.comp_apply,sub_div,mul_div_cancel_left₀ _ nonzero,sub_add_cancel]

/-- The same original full polarization, including the entire residual, consumes the actual cofactor column limit. -/
theorem sourceNativeCurvature_sheet (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (r : Fin 36) :
    Tendsto (fun e : scaleDomain=>
      (2*(sourceSheet branch n unit e.val:ℂ))*
        (originalReader36 (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
          sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) r/(e.val:ℂ)^2)
      scaleApproach (𝓝 ((sourceMatrix (sourceSlowCurvatureTerms++sourceFastCurvatureTerms)
        (physicalFrequencyMomentum (sourceSpeed branch) n)*ᵥ
        fiveVector (regularScaling 0*ᵥ
          (Matrix.single (residueIndex branch) (residueIndex branch) (softCoefficient branch:ℂ)*ᵥ
            Pi.single (residueIndex branch) (1:ℂ)))) (Fin.castLE (by decide) r))) := by
  have coordinates:=sourcePoleCoordinates_sheet branch n unit
  have terms (j : Fin 289) := (sourceCurvatureFrame_divided branch n unit r j).mul
    (tendsto_pi_nhds.mp coordinates j)
  have combined:=tendsto_finsetSum Finset.univ (fun j _=>terms j)
  apply combined.congr'
  filter_upwards [] with e
  rw [sourceNativeFrequencyPolarization_frame branch e.val _ n e.property.1.ne']
  have multiplication :
      (originalReader36 (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
        (sourceNativeFrame (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
          sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n)) r=
      ∑j : Fin 289,sourceCurvatureFrame (frequencyRay e.val (sourceSheet branch n unit e.val) n) r j*
        sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n j := by
    simp only [sourceCurvatureFrame,Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [multiplication]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem zeroScaling_single (j : Fin 5) (slow : j.val<3) (a : ℂ) :
    regularScaling 0*ᵥPi.single j a=Pi.single j a := by
  funext i
  rw [Matrix.mulVec_single]
  by_cases same : i=j
  · subst i
    simp [regularScaling,slow]
  · simp_all [regularScaling]

private theorem five_single (j : Fin 5) (a : ℂ) :
    fiveVector (Pi.single j a)=Pi.single (fiveIndex j) a := by
  funext i
  by_cases inside : i.val<5
  · simp [fiveVector,inside,Pi.single_apply,fiveIndex,Fin.ext_iff]
  · have different : fiveIndex j≠i := by
      intro same
      have equal:=congrArg Fin.val same
      simp only [fiveIndex] at equal
      omega
    simp [fiveVector,inside,different]

private theorem sourcePoleCoordinates_origin (branch : Fin 2) :
    fiveVector (regularScaling 0*ᵥ
      (Matrix.single (residueIndex branch) (residueIndex branch) (softCoefficient branch:ℂ)*ᵥ
        Pi.single (residueIndex branch) (1:ℂ)))=
      Pi.single (fiveIndex (residueIndex branch)) (softCoefficient branch:ℂ) := by
  rw [Matrix.single_mulVec]
  simp only [Pi.single_eq_same,mul_one]
  change fiveVector (regularScaling 0*ᵥPi.single (residueIndex branch) (softCoefficient branch:ℂ))=_
  rw [zeroScaling_single _ (by fin_cases branch <;> simp [residueIndex]),five_single]

/-- This is the actual source-normalized surviving coefficient, not an assigned charge or selected eigenvector. -/
def sourceCurvaturePoleLimit (branch : Fin 2) (n : PhysicalMomentum) (r : Fin 36) : ℂ :=
  sourceMatrix (sourceSlowCurvatureTerms++sourceFastCurvatureTerms)
    (physicalFrequencyMomentum (sourceSpeed branch) n) (Fin.castLE (by decide) r)
    (fiveIndex (residueIndex branch))*(softCoefficient branch:ℂ)

/-- The exact source residue and physical ray choose the limit; fast and full residual were priced first. -/
theorem sourceCurvaturePoleLimit_generated (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (r : Fin 36) :
    Tendsto (fun e : scaleDomain=>
      (2*(sourceSheet branch n unit e.val:ℂ))*
        (originalReader36 (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
          sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) r/(e.val:ℂ)^2)
      scaleApproach (𝓝 (sourceCurvaturePoleLimit branch n r)) := by
  have original:=sourceNativeCurvature_sheet branch n unit r
  rw [sourcePoleCoordinates_origin,Matrix.mulVec_single] at original
  exact original

/-- The original branch0 cofactor selects the actually cancelled middle slow column, without asserting whole-field zero. -/
theorem sourceCurvaturePoleLimit_zero (n : PhysicalMomentum) (r : Fin 36) : sourceCurvaturePoleLimit 0 n r=0 := by
  norm_num [sourceCurvaturePoleLimit,residueIndex,fiveIndex,sourceMatrix,sourceSlowCurvatureTerms,
    sourceFastCurvatureTerms,SourceTerm.matrix,Matrix.single_apply,Fin.ext_iff]

/-- Branch1 retains the actual ordinary-source spatial triple, including its source kinetic normalization. -/
theorem sourceCurvaturePoleLimit_one (n : PhysicalMomentum) (r : Fin 36) :
    sourceCurvaturePoleLimit 1 n r=
      (if r.val=33 then (5/9:ℂ)*rootTwo*Complex.I*(n 0:ℂ)
       else if r.val=34 then (5/9:ℂ)*rootTwo*Complex.I*(n 1:ℂ)
       else if r.val=35 then (5/9:ℂ)*rootTwo*Complex.I*(n 2:ℂ) else 0)*(softCoefficient 1:ℂ) := by
  unfold sourceCurvaturePoleLimit
  congr 1
  norm_num [residueIndex,fiveIndex,sourceMatrix,sourceSlowCurvatureTerms,sourceFastCurvatureTerms,
    SourceTerm.matrix,Matrix.single_apply,Fin.ext_iff,Powers.value,coefficientValue,physicalFrequencyMomentum]
  by_cases h33 : r.val=33
  · have same : r=(33:Fin 36):=Fin.ext h33
    subst r
    norm_num
    change (5/9:ℂ) * rootTwo * (Complex.I * (n 0:ℂ)) = (5/9:ℂ) * rootTwo * Complex.I * (n 0:ℂ)
    ring
  by_cases h34 : r.val=34
  · have same : r=(34:Fin 36):=Fin.ext h34
    subst r
    norm_num
    change (5/9:ℂ) * rootTwo * (Complex.I * (n 1:ℂ)) = (5/9:ℂ) * rootTwo * Complex.I * (n 1:ℂ)
    ring
  by_cases h35 : r.val=35
  · have same : r=(35:Fin 36):=Fin.ext h35
    subst r
    norm_num
    change (5/9:ℂ) * rootTwo * (Complex.I * (n 2:ℂ)) = (5/9:ℂ) * rootTwo * Complex.I * (n 2:ℂ)
    ring
  norm_num [h33,h34,h35,Ne.symm h33,Ne.symm h34,Ne.symm h35]

open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalPhaseGaugeRealization

/-- The left source forcing at the same generated origin, retaining the complete original readback. -/
def sourceCurvatureEmitterInput (forcing : Fin 289→ℂ) : Fin 5→ℂ :=
  regularScaling 0*ᵥ(fun i=>(slowFastFrame.transpose*ᵥ(rawEffectiveReader 0*ᵥactiveForcing 0 forcing)) (fiveIndex i))

private theorem sourceSoftInput_sheet (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (forcing : Fin 289→ℂ) :
    Tendsto (fun e : scaleDomain=>softForcing e.val (sourceSheet branch n unit e.val) n forcing)
      scaleApproach (𝓝 (sourceCurvatureEmitterInput forcing)) := by
  have ray:=sourceRay_soft_limit branch n unit
  have kernel : Tendsto (fun e : scaleDomain=>activeKernel (frequencyRay e.val (sourceSheet branch n unit e.val) n))
      scaleApproach (𝓝 (activeKernel 0)) := (sourceMatrix_continuous activeTerms).continuousAt.tendsto.comp ray
  have inverse:=unrestrictedGreen_smooth_origin.continuousAt.tendsto.comp ray
  have reader : Tendsto (fun e : scaleDomain=>rawEffectiveReader (frequencyRay e.val (sourceSheet branch n unit e.val) n))
      scaleApproach (𝓝 (rawEffectiveReader 0)) := by
    exact tendsto_const_nhds.sub ((tendsto_const_nhds.mul kernel).mul inverse)
  have back : Tendsto (fun e : scaleDomain=>originalReadback (frequencyRay e.val (sourceSheet branch n unit e.val) n))
      scaleApproach (𝓝 (originalReadback 0)) :=
    (((sourceMatrix_continuous originalChangeTerms).comp continuous_neg).matrix_transpose).continuousAt.tendsto.comp ray
  have active:=mulVec_limit (tendsto_const_nhds (x:=activeProjection))
    (mulVec_limit back (tendsto_const_nhds (x:=forcing)))
  have read:=mulVec_limit reader active
  have moved:=mulVec_limit (tendsto_const_nhds (x:=slowFastFrame.transpose)) read
  have selected : Tendsto
      (fun e : scaleDomain=>fun i : Fin 5=>(slowFastFrame.transpose*ᵥ(rawEffectiveReader
        (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
          activeForcing (frequencyRay e.val (sourceSheet branch n unit e.val) n) forcing)) (fiveIndex i))
      scaleApproach (𝓝 (fun i : Fin 5=>(slowFastFrame.transpose*ᵥ(rawEffectiveReader 0*ᵥactiveForcing 0 forcing)) (fiveIndex i))) :=
    tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mp moved (fiveIndex i))
  exact mulVec_limit (scaling_continuous.continuousAt.tendsto.comp scaleVal_tendsto) selected

private theorem leading_pivot (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    leadingResidue branch n (residueIndex branch) (residueIndex branch)≠0 := by
  have diagonal:=congrFun (congrFun (leadingResidue_normalization branch n unit) (residueIndex branch)) (residueIndex branch)
  simp only [Matrix.smul_apply,Matrix.single_apply,smul_eq_mul] at diagonal
  intro zero
  rw [zero,mul_zero] at diagonal
  exact (Complex.ofReal_ne_zero.mpr (softCoefficient_nonzero branch)) diagonal.symm

private theorem leading_left_read (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (v : Fin 5→ℂ) :
    (leadingResidue branch n*ᵥv) (residueIndex branch)/
      leadingResidue branch n (residueIndex branch) (residueIndex branch)=v (residueIndex branch) := by
  have diagonal:=congrFun (congrFun (leadingResidue_normalization branch n unit) (residueIndex branch)) (residueIndex branch)
  simp only [Matrix.smul_apply,Matrix.single_apply,smul_eq_mul] at diagonal
  have scale : 2*(sourceSpeed branch:ℂ)≠0 := by
    intro zero
    rw [zero,zero_mul] at diagonal
    exact (Complex.ofReal_ne_zero.mpr (softCoefficient_nonzero branch)) diagonal.symm
  have column:=congrFun (congrArg (fun A : Matrix (Fin 5) (Fin 5) ℂ=>A*ᵥv)
    (leadingResidue_normalization branch n unit)) (residueIndex branch)
  simp only [Matrix.smul_mulVec,Matrix.single_mulVec,Pi.smul_apply,Function.update_self,smul_eq_mul] at column
  apply (div_eq_iff (leading_pivot branch n unit)).mpr
  apply (mul_left_cancel₀ scale)
  rw [column]
  calc
    (softCoefficient branch:ℂ)*v (residueIndex branch)=
      (2*(sourceSpeed branch:ℂ)*leadingResidue branch n (residueIndex branch) (residueIndex branch))*v (residueIndex branch) :=
        congrArg (fun z : ℂ=>z*v (residueIndex branch)) diagonal.symm
    _= _ := by ring

/-- The actual left cofactor is priced with epsilon squared; no constancy or nonzero emitter is assumed. -/
theorem sourcePhotonLeftReader_sheet (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (forcing : Fin 289→ℂ) :
    Tendsto (fun e : scaleDomain=>(e.val:ℂ)^2*sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n forcing)
      scaleApproach (𝓝 (sourceCurvatureEmitterInput forcing (residueIndex branch))) := by
  have residue:=sourceResidue_soft_limit branch n unit
  have product:=mulVec_limit residue (sourceSoftInput_sheet branch n unit forcing)
  have numerator:=tendsto_pi_nhds.mp product (residueIndex branch)
  have denominator:=tendsto_pi_nhds.mp (tendsto_pi_nhds.mp residue (residueIndex branch)) (residueIndex branch)
  have ratio:=numerator.div denominator (leading_pivot branch n unit)
  rw [leading_left_read branch n unit] at ratio
  apply ratio.congr'
  filter_upwards [] with e
  simp only [Pi.div_apply]
  rw [←softForcing_generated e.val _ n e.property.1.ne' forcing,Matrix.mulVec_smul]
  simp only [sourcePhotonLeftReader,sourceNativePoleCoefficient,Pi.smul_apply,smul_eq_mul,mul_div_assoc]

/-- The true current-emitted field now consumes both the full physical curvature limit and its actual left cofactor price. -/
theorem sourceActualCurrentCurvature_sheet (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (r : Fin 36) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      sourceGaugePhotonCurvature q sL eL sR eR pL pR lambda T e.val (sourceSheet branch n unit e.val) n r)
      scaleApproach (𝓝 (sourceCurvatureEmitterInput
        (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) (residueIndex branch)*sourceCurvaturePoleLimit branch n r)) := by
  have left:=sourcePhotonLeftReader_sheet branch n unit (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)
  have right:=sourceCurvaturePoleLimit_generated branch n unit r
  have generated:=left.mul right
  apply generated.congr'
  filter_upwards [sourceGaugePhotonCurvature_generated q sL eL sR eR pL pR lambda T branch n unit] with e factor
  have row:=congrFun factor r
  rw [row]
  simp only [Pi.smul_apply,smul_eq_mul]
  have nonzero : (e.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [nonzero]

end LowEnergy.PreparationPhysicalCurvatureSheetLimit
