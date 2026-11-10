import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMStaticCorrectionPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMCorrectedCouplingSource
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationCoordinates PreparationVacuumMixedFieldReturn PreparationVacuumGaugeSourceInjection
open ActualEMCarrierOwn ActualEMAction PhysicalEMGaugeRealization SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMNativeSchurClock
open ActualDressedEMNativePrincipal ActualDressedEMNativeMomentum ActualDressedEMNativeCoulomb
open ActualDressedEMPhysicalResidueFlux ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux
open ActualDressedNoetherCoulombUnit ActualDressedOrderedStatic ActualCompositeFieldCurrent
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] correctedPhysicalClock correctedPhysicalClockJet emFullPhysicalResidue
  emFullAnalyticColumnNumerator emPhysicalCorrectedPoleCoefficient emPhysicalNormalizedPoleColumnCoefficient

/-- The source spatial constraint projection acts on arbitrary fields, retaining the temporal equation separately. -/
def nativeTransverseRead (k : PhysicalMomentum) (v : Fin 4 → ℂ) : Fin 3 → ℂ :=
  fun i => v i.succ-(k i : ℂ)*nativeSpatialContraction k v/(spatialSquare k : ℂ)

/-- Gauss/time-space/longitudinal terms cancel inside this projection of the same original principal, without assuming a transverse input. -/
theorem actual_native_transverse_source_symbol (omega : ℝ) (k : PhysicalMomentum) (v : Fin 4 → ℂ)
    (q_ne : spatialSquare k≠0) :
    nativeTransverseRead k (nativePhysicalEMPrincipal omega k v)=
      (2*(lapse : ℂ)*((omega : ℂ)^2-(nativePrimitiveSpeed : ℂ)^2*(spatialSquare k : ℂ))) •
        nativeTransverseRead k v := by
  have kZero (h : 0<3) : k (⟨0,h⟩ : Fin 3)=k 0 := rfl
  have kOne (h : 1<3) : k (⟨1,h⟩ : Fin 3)=k 1 := rfl
  have kTwo (h : 2<3) : k (⟨2,h⟩ : Fin 3)=k 2 := rfl
  have vOne (h : 1<4) : v (⟨1,h⟩ : Fin 4)=v 1 := rfl
  have vTwo (h : 2<4) : v (⟨2,h⟩ : Fin 4)=v 2 := rfl
  have vThree (h : 3<4) : v (⟨3,h⟩ : Fin 4)=v 3 := rfl
  have qn : (spatialSquare k : ℂ)≠0 := Complex.ofReal_ne_zero.mpr q_ne
  have square : (spatialSquare k : ℂ)=(k 0 : ℂ)^2+(k 1 : ℂ)^2+(k 2 : ℂ)^2 := by
    simp only [spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]
  rw [square] at qn
  have ln : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  funext i
  fin_cases i <;> simp only [nativeTransverseRead,nativePhysicalEMPrincipal,nativeSpatialContraction,
    nativePrimitiveSpeed,Complex.ofReal_inv,Pi.smul_apply,smul_eq_mul,spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]
  all_goals dsimp only [Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.succ]
  all_goals simp only [eq_mpr_eq_cast,cast_eq,kZero,kOne,kTwo,vOne,vTwo,vThree]
  all_goals generalize hl : (lapse : ℂ)=L at ln ⊢
  all_goals field_simp [qn,ln]
  all_goals ring1

/-- Physical propagation is read from the actual root frequency and momentum, before any speed calibration. -/
def actualRootPhaseSpeedSquared (eps s : ℝ) (n : PhysicalMomentum) : ℝ :=
  (sourceFrequency eps s)^2/spatialSquare ((eps^2 : ℝ) • n)

/-- The original actual EM root consumes the explicit source correction before any scalar dispersion assertion. -/
theorem actual_corrected_root_principal_source (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n)
      (emInsertion.transpose*ᵥactualEMZeroClockMode event eps n nu (s : ℂ))=
      nativeEMRestInsertion.transpose*ᵥnativeCompleteCorrection (frequencyRay eps s n)
        (zeroClockQuantumResponse event eps s n) (actualEMZeroClockMode event eps n nu (s : ℂ)) := by
  have source := actual_native_forced_principal (frequencyRay eps s n)
    (zeroClockQuantumResponse event eps s n) (actualEMZeroClockMode event eps n nu (s : ℂ))
  have kernel : (emOriginalJacobi (frequencyRay eps s n)-zeroClockQuantumResponse event eps s n)*ᵥ
      actualEMZeroClockMode event eps n nu (s : ℂ)=0 := by
    rw [Matrix.sub_mulVec,actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root,sub_self]
  rw [kernel] at source
  have zero : nativeCompleteForceRead (frequencyRay eps s n) 0=0 := by
    rw [nativeCompleteForceRead]
    have r : emRestSlice 0=0 := rfl
    have b : emAuxiliarySlice 0=0 := rfl
    rw [r,b,Matrix.mulVec_zero,Matrix.mulVec_zero,sub_zero]
  rw [zero,Matrix.mulVec_zero,zero_add] at source
  have physical : nativeEMMomentumMatrix (frequencyRay eps s n)*ᵥ
      (emInsertion.transpose*ᵥactualEMZeroClockMode event eps n nu (s : ℂ))=
      nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n)
        (emInsertion.transpose*ᵥactualEMZeroClockMode event eps n nu (s : ℂ)) := by
    rw [← actual_physical_frequency_ray,actual_native_physical_em_principal]
  rw [physical] at source
  exact source

/-- Corrected phase-speed correction is generated by the same full Q/background/lower source as the static coupling correction. No c0 replacement or isotropic/scalar pole is assumed. -/
theorem actual_corrected_root_speed_source (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (q_ne : spatialSquare ((eps^2 : ℝ) • n)≠0) :
    (2*(lapse : ℂ)*(spatialSquare ((eps^2 : ℝ) • n) : ℂ)*
      ((actualRootPhaseSpeedSquared eps s n : ℂ)-(nativePrimitiveSpeed : ℂ)^2)) •
        nativeTransverseRead ((eps^2 : ℝ) • n)
          (emInsertion.transpose*ᵥactualEMZeroClockMode event eps n nu (s : ℂ))=
      nativeTransverseRead ((eps^2 : ℝ) • n)
        (nativeEMRestInsertion.transpose*ᵥnativeCompleteCorrection (frequencyRay eps s n)
          (zeroClockQuantumResponse event eps s n) (actualEMZeroClockMode event eps n nu (s : ℂ))) := by
  have source := congrArg (nativeTransverseRead ((eps^2 : ℝ) • n))
    (actual_corrected_root_principal_source event eps s n mu nu balanced finite regular root)
  rw [actual_native_transverse_source_symbol _ _ _ q_ne] at source
  have coefficient : 2*(lapse : ℂ)*((sourceFrequency eps s : ℂ)^2-
      (nativePrimitiveSpeed : ℂ)^2*(spatialSquare ((eps^2 : ℝ) • n) : ℂ))=
      2*(lapse : ℂ)*(spatialSquare ((eps^2 : ℝ) • n) : ℂ)*
        ((actualRootPhaseSpeedSquared eps s n : ℂ)-(nativePrimitiveSpeed : ℂ)^2) := by
    simp only [actualRootPhaseSpeedSquared,Complex.ofReal_div,Complex.ofReal_pow]
    field_simp [Complex.ofReal_ne_zero.mpr q_ne]
  rw [coefficient] at source
  exact source

/-- On an actual nonzero transverse coordinate chart, the corrected root speed is explicitly priced by its full source feedback. -/
theorem actual_corrected_root_speed_component_price (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (q_ne : spatialSquare ((eps^2 : ℝ) • n)≠0) (i : Fin 3)
    (coordinate_ne : nativeTransverseRead ((eps^2 : ℝ) • n)
      (emInsertion.transpose*ᵥactualEMZeroClockMode event eps n nu (s : ℂ)) i≠0) :
    (actualRootPhaseSpeedSquared eps s n : ℂ)=(nativePrimitiveSpeed : ℂ)^2+
      nativeTransverseRead ((eps^2 : ℝ) • n)
        (nativeEMRestInsertion.transpose*ᵥnativeCompleteCorrection (frequencyRay eps s n)
          (zeroClockQuantumResponse event eps s n) (actualEMZeroClockMode event eps n nu (s : ℂ))) i/
        (2*(lapse : ℂ)*(spatialSquare ((eps^2 : ℝ) • n) : ℂ)*nativeTransverseRead ((eps^2 : ℝ) • n)
          (emInsertion.transpose*ᵥactualEMZeroClockMode event eps n nu (s : ℂ)) i) := by
  have value := congrFun (actual_corrected_root_speed_source event eps s n mu nu balanced finite regular root q_ne) i
  simp only [Pi.smul_apply,smul_eq_mul] at value
  have ln : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  generalize hl : (lapse : ℂ)=L at ln value ⊢
  field_simp [ln,Complex.ofReal_ne_zero.mpr q_ne,coordinate_ne]
  linear_combination value

/-- Every original physical pole order remains in the flux source, including the complete quantum clock jet. -/
def actualFullPhysicalFlux (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (nu : Fin 4) : Fin 289 → ℂ :=
  correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ)+
    ∑r∈Finset.range (emFullColumnPoleOrder event eps n nu (s : ℂ)-1),
      emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ) (r+2)*ᵥ
        emPhysicalNormalizedPoleColumnCoefficient event eps n nu (s : ℂ)
          (emFullColumnPoleOrder event eps n nu (s : ℂ)-(r+2))

private theorem forcing_read_add (p : Fin 4 → ℂ) (f g : Fin 289 → ℂ) :
    nativeCompleteForceRead p (f+g)=nativeCompleteForceRead p f+nativeCompleteForceRead p g := by
  have r : emRestSlice (f+g)=emRestSlice f+emRestSlice g := rfl
  have b : emAuxiliarySlice (f+g)=emAuxiliarySlice f+emAuxiliarySlice g := rfl
  rw [nativeCompleteForceRead,r,b,Matrix.mulVec_add,Matrix.mulVec_add]
  unfold nativeCompleteForceRead
  abel

private theorem original_auxiliary_em_input_zero (nu : Fin 4) :
    emAuxiliarySlice (fun i => emInsertion i nu)=0 := by
  funext i
  have ne (a : Fin 12) : gaugeAuxiliaryIndex i≠gaugeSlot nu a := by
    intro same
    have val := congrArg Fin.val same
    change 217+12*i.1.val+i.2.val=9+12*nu.val+a.val at val
    omega
  simp only [emAuxiliarySlice,emInsertion,emGaugeField,Finset.sum_apply,Pi.smul_apply,gaugeField,
    Pi.single_apply,ne,if_false,smul_zero,Finset.sum_const_zero,Complex.ofReal_zero,Pi.zero_apply]

private theorem observed_em_forcing (p : Fin 4 → ℂ) (nu : Fin 4) :
    nativeEMRestInsertion.transpose*ᵥnativeCompleteForceRead p (fun i => emInsertion i nu)=
      (3/4 : ℂ) • Pi.single nu 1 := by
  rw [nativeCompleteForceRead,original_auxiliary_em_input_zero,Matrix.mulVec_zero,Matrix.mulVec_zero,sub_zero,
    actual_complete_em_observation]
  funext mu
  have paid := congrFun (congrFun ActualEMCurrentSplit.em_coordinate_gram mu) nu
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,
    Pi.smul_apply,smul_eq_mul,Pi.single_apply,Matrix.mulVec,dotProduct] using paid

/-- The actual corrected clock jet and canonical residue are normalized through the same native source read, with the analytic column and all higher principal orders retained. -/
theorem actual_corrected_physical_schur_flux (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    let a : Fin 289 → ℂ := fun i => (emFullAnalyticColumnNumerator event eps n nu (s : ℂ) i).eval (s : ℂ)/
      (emColumnDenominatorTail event eps n (s : ℂ)).eval (s : ℂ)
    nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n) (emInsertion.transpose*ᵥa)+
      nativeEMRestInsertion.transpose*ᵥnativeCompleteForceRead (frequencyRay eps s n)
        (actualFullPhysicalFlux event eps s n nu)=
      ((3/4 : ℂ) • Pi.single nu 1)+
      nativeEMRestInsertion.transpose*ᵥnativeCompleteCorrection (frequencyRay eps s n)
        (zeroClockQuantumResponse event eps s n) a := by
  dsimp only
  let a : Fin 289 → ℂ := fun i => (emFullAnalyticColumnNumerator event eps n nu (s : ℂ) i).eval (s : ℂ)/
    (emColumnDenominatorTail event eps n (s : ℂ)).eval (s : ℂ)
  have point : sourceFrequency eps s/eps^2=s := by
    unfold sourceFrequency
    exact mul_div_cancel_left₀ s (pow_ne_zero 2 eps_ne)
  have physicalRegular : (zeroClockClearing event eps n).eval ((sourceFrequency eps s/eps^2 : ℝ) : ℂ)≠0 := by
    simpa only [point] using regular
  have matrix : correctedPhysicalClock event eps (sourceFrequency eps s) n=
      emOriginalJacobi (frequencyRay eps s n)-zeroClockQuantumResponse event eps s n := by
    rw [actual_corrected_physical_threshold _ _ _ _ eps_ne physicalRegular,point,
      actual_zero_clock_threshold_quantum _ _ _ _ regular]
  have full : correctedPhysicalClock event eps (sourceFrequency eps s) n*ᵥa+
      actualFullPhysicalFlux event eps s n nu=(fun i => emInsertion i nu) := by
    simpa only [actualFullPhysicalFlux,a,add_assoc] using
      actual_em_original_physical_residue_balance event eps s n mu nu eps_ne balanced finite regular root
  rw [matrix] at full
  have observed := congrArg (fun v : Fin 289 → ℂ => nativeEMRestInsertion.transpose*ᵥ
    nativeCompleteForceRead (frequencyRay eps s n) v) full
  rw [forcing_read_add,Matrix.mulVec_add,observed_em_forcing] at observed
  have principal := actual_native_forced_principal (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n) a
  have physical : nativeEMMomentumMatrix (frequencyRay eps s n)*ᵥ(emInsertion.transpose*ᵥa)=
      nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n) (emInsertion.transpose*ᵥa) := by
    rw [← actual_physical_frequency_ray,actual_native_physical_em_principal]
  rw [physical] at principal
  change nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n) (emInsertion.transpose*ᵥa)+
    _=((3/4 : ℂ) • Pi.single nu 1)+_ 
  linear_combination principal+observed

/-- The physical speed read comes from the actual source frequency/momentum; the consumer above owns its corrected-root interpretation. -/
def actualRootPhaseSpeed (eps s : ℝ) (n : PhysicalMomentum) : ℝ :=
  Real.sqrt (actualRootPhaseSpeedSquared eps s n)

/-- Full source ordered coupling read in the original physical h and actual root propagation units. Electron calibration, other EM entries and non-pure pieces are not discarded. -/
def actualFullRootCouplingRead (event : DressedEvent) (eps s : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  (sourceOrderedProbeCoefficient event n pd ps dL dR sL sR/(4*(Real.pi : ℂ)))/
    ((Stage10.ActionNormalization.phaseMomentum : ℂ)*(actualRootPhaseSpeed eps s n : ℂ))

/-- The preserved full coupling read uses the source-generated static correction balance and the same original h/physical root speed, retaining all16 EM and non-pure channels. -/
theorem actual_full_root_coupling_balance (event : DressedEvent) (eps s : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    actualFullRootCouplingRead event eps s n pd ps dL dR sL sR=
      (sourceInputCharge dR*sourceInputCharge sR+
        noetherChargeCalibration pd dL dR*sourceInputCharge sR+
        sourceInputCharge dR*noetherChargeCalibration ps sL sR+
        noetherChargeCalibration pd dL dR*noetherChargeCalibration ps sL sR)*
        (nativeDirectionalOrderedCoulomb n+actualNativeCoulombCorrection event n)/
          ((Stage10.ActionNormalization.phaseMomentum : ℂ)*(actualRootPhaseSpeed eps s n : ℂ))+
      (otherEMCoefficient event n pd ps dL dR sL sR+noetherNonPureCoefficient event n pd ps dL dR sL sR)/
        ((4*(Real.pi : ℂ))*((Stage10.ActionNormalization.phaseMomentum : ℂ)*(actualRootPhaseSpeed eps s n : ℂ))) := by
  rw [actualFullRootCouplingRead,actual_noether_native_coulomb_balance]
  ring1

end LowEnergy.GaussComposite.ActualDressedEMCorrectedCouplingSource
