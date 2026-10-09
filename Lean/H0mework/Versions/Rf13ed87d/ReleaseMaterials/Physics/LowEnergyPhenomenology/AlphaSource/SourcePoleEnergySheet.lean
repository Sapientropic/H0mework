import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePolePreparedMatrix

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalPoleChargeMatrix
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalCurvatureSheetLimit PreparationPhysicalNormalizedFullField
open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumActionFieldLift
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin
open PreparationVacuumMixedControl
open PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumFullSlowFieldResponse
open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor CanonicalGradedSpatialSource
open PreparationVacuumNonlinearFieldCurve PreparationVacuumPhysicalFeedback
open PreparationVacuumSourceFieldFamily GaussHistoryHilbert PreparationVacuumActualFieldQuantization
open GaussQuantumMultiplier GaussFockLift GaussCoreHilbert SourceQuantumFockGauge
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceChargedNativeFrameJet sourceChargedNativeFrameResidual sourceNativeFrequencyPolarization sourcePoleCoordinates

private theorem matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
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

private theorem jet_continuous : Continuous sourceChargedNativeFrameJet := by
  have original:=matrix_continuous (degreeTerms (positiveTerms originalChangeTerms) 1)
  have active:=matrix_continuous (degreeTerms (positiveTerms activeTerms) 1)
  change Continuous (sourceLinearPart originalChangeTerms) at original
  change Continuous (sourceLinearPart activeTerms) at active
  unfold sourceChargedNativeFrameJet
  exact ((original.mul continuous_const).sub
    (((continuous_const.mul continuous_const).mul active).mul continuous_const)).mul continuous_const

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
  exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp matrix i) j).mul (tendsto_pi_nhds.mp vector j)

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

private theorem coordinates_origin (branch : Fin 2) :
    fiveVector (regularScaling 0*ᵥ
      (Matrix.single (residueIndex branch) (residueIndex branch) (softCoefficient branch:ℂ)*ᵥ
        Pi.single (residueIndex branch) (1:ℂ)))=
      Pi.single (fiveIndex (residueIndex branch)) (softCoefficient branch:ℂ) := by
  rw [Matrix.single_mulVec]
  simp only [Pi.single_eq_same,mul_one]
  change fiveVector (regularScaling 0*ᵥPi.single (residueIndex branch) (softCoefficient branch:ℂ))=_
  rw [zeroScaling_single _ (by fin_cases branch <;> simp [residueIndex]),five_single]

/-- The source cofactor selects its original slow column after actual fast epsilon scaling. -/
theorem sourcePoleCoordinate_unit_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ)) •
      sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n)
      scaleApproach (𝓝 (Pi.single (fiveIndex (residueIndex branch)) (softCoefficient branch:ℂ))) := by
  simpa only [coordinates_origin] using sourcePoleCoordinates_sheet branch n unit

/-- The whole native-frame residual is priced after the actual, nonconstant cofactor contraction. -/
theorem sourcePoleResidual_sheet (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (i : Fin 289) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      sourcePoleFrameResidual branch e.val (sourceSheet branch n unit e.val) n i/(e.val:ℂ)^2)
      scaleApproach (𝓝 0) := by
  have matrix : Tendsto (fun e : scaleDomain=>fun i j : Fin 289=>
      sourceChargedNativeFrameResidual ((e.val:ℂ)^2) (physicalFrequencyMomentum (sourceSheet branch n unit e.val) n) i j/(e.val:ℂ)^2)
      scaleApproach (𝓝 (0:Matrix (Fin 289) (Fin 289) ℂ)) :=
    tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr (fun j=>sourceNativeFrameResidual_sheet branch n unit i j))
  have result:=tendsto_pi_nhds.mp (mulVec_limit matrix (sourcePoleCoordinate_unit_limit branch n unit)) i
  simp only [Matrix.zero_mulVec,Pi.zero_apply] at result
  apply result.congr'
  filter_upwards [] with e
  simp only [sourcePoleFrameResidual,Matrix.mulVec, dotProduct,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The complete first jet consumes the actual moving sheet and all five pole coordinates. -/
theorem sourcePoleJet_sheet (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ)) •
      sourcePoleJetField branch e.val (sourceSheet branch n unit e.val) n)
      scaleApproach (𝓝 (sourceChargedNativeFrameJet (physicalFrequencyMomentum (sourceSpeed branch) n)*ᵥ
        Pi.single (fiveIndex (residueIndex branch)) (softCoefficient branch:ℂ))) := by
  have matrix:=jet_continuous.continuousAt.tendsto.comp (sourceCurvatureDirection_tendsto branch n unit)
  have result:=mulVec_limit matrix (sourcePoleCoordinate_unit_limit branch n unit)
  simpa only [sourcePoleJetField,Matrix.mulVec_smul,Function.comp_def] using result

/-- The original origin field remains explicit; the full field supplies its physically divided first return. -/
theorem sourcePoleField_first_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (i : Fin 289) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n i-
        sourcePoleOriginField branch e.val (sourceSheet branch n unit e.val) n i)/(e.val:ℂ)^2)
      scaleApproach (𝓝 ((sourceChargedNativeFrameJet (physicalFrequencyMomentum (sourceSpeed branch) n)*ᵥ
        Pi.single (fiveIndex (residueIndex branch)) (softCoefficient branch:ℂ)) i)) := by
  have result:=(tendsto_pi_nhds.mp (sourcePoleJet_sheet branch n unit) i).add (sourcePoleResidual_sheet branch n unit i)
  rw [add_zero] at result
  apply result.congr'
  filter_upwards [] with e
  have original:=congrFun (sourceNativeFrequencyPolarization_firstReturn branch e.val
    (sourceSheet branch n unit e.val) n e.property.1.ne') i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at original ⊢
  have nonzero : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  symm
  apply (div_eq_iff (pow_ne_zero 2 nonzero)).mpr
  rw [←original]
  field_simp [nonzero]
  ring

private theorem energyRead_linear (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (i j : ActualPreparedIndex) (V : Fin 289→ℂ) :
    sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2 V=
      ∑k : Fin 289,V k*sourceNormalizedEnergySymbol p (sourceState sourcePoint.val) (fieldDirection (fieldUnit k))
        (Sum.inl (sourceChargedQuantumIndex i.1 i.2)) (Sum.inl (sourceChargedQuantumIndex j.1 j.2)) := by
  simp only [sourceFullEnergyRead,sourceChargedEnergyRead_entry,sourceFullEnergyMatrix,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]

/-- The actual fullCAR/Gauss energy reader consumes the whole field first return with its original origin kept explicit. -/
theorem sourcePoleEnergy_first_limit (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (i j : ActualPreparedIndex) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)-
      sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePoleOriginField branch e.val (sourceSheet branch n unit e.val) n))/(e.val:ℂ)^2)
      scaleApproach (𝓝 (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourceChargedNativeFrameJet (physicalFrequencyMomentum (sourceSpeed branch) n)*ᵥ
          Pi.single (fiveIndex (residueIndex branch)) (softCoefficient branch:ℂ)))) := by
  have continuousRead : Continuous (fun V : Fin 289→ℂ=>sourceFullEnergyRead epsilon precision p
      (sourceState sourcePoint.val) i.1 i.2 j.1 j.2 V) := by
    simp only [energyRead_linear]
    fun_prop
  have field:=tendsto_pi_nhds.mpr (sourcePoleField_first_limit branch n unit)
  have result:=continuousRead.continuousAt.tendsto.comp field
  apply result.congr'
  filter_upwards [] with e
  simp only [Function.comp_apply,energyRead_linear]
  rw [←Finset.sum_sub_distrib]
  simp only [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

end LowEnergy.PreparationPhysicalPoleChargeMatrix
