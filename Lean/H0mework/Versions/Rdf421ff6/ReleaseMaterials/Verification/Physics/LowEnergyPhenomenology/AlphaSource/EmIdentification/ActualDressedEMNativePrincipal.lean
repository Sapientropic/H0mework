import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeClockSecond

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativePrincipal
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open SourcePropagationNativeActionHessian ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMClockDispersion
open ActualDressedEMNativeSchurClock ActualEMCarrierOwn ActualEMCurrentSplit
open PhysicalEMGaugeRealization PreparationVacuumPhysicalPoleSheet
open PreparationCoordinates SourceQuantumGaugeSliceCoordinates StageNineHolonomicField
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedZeroClockFrequency
open LowEnergy.ActualDressedVisiblePole ActualDressedFullCoulomb ActualDressedZeroClockVector
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

private theorem lie_inverse_scale (z : ℂ) (v : Fin 12 → ℂ) :
    auxiliaryLieInverse (fun a => z*v a)=fun a => z*auxiliaryLieInverse v a := by
  funext a
  unfold auxiliaryLieInverse
  split_ifs <;> ring1

private theorem lie_reader_scale (z : ℂ) (v : Fin 12 → ℂ) :
    auxiliaryLieReader (fun a => z*v a)=fun a => z*auxiliaryLieReader v a := by
  funext a
  unfold auxiliaryLieReader
  split_ifs <;> ring1

/-- The fixed source inverse consumes all original auxiliary time rows before an EM projection. -/
theorem actual_native_inverse_time_reader (k : PhysicalMomentum) (r : Fin 217 → ℂ)
    (p : Fin 6) (a : Fin 12) :
    (nativeAuxiliaryInverseMatrix*ᵥ(nativeAuxiliaryRestClockFirst k*ᵥr)) (p,a)=
      if p=3 then 2*Complex.I*(lapse : ℂ)*r (gaugeRestIndex 1 a) else
      if p=4 then 2*Complex.I*(lapse : ℂ)*r (gaugeRestIndex 2 a) else
      if p=5 then 2*Complex.I*(lapse : ℂ)*r (gaugeRestIndex 3 a) else 0 := by
  rw [native_auxiliary_inverse_matrix_action,actual_native_auxiliary_time_reader]
  fin_cases p <;>
    simp only [nativeAuxiliaryInverse,nativeAuxiliaryWeight,Fin.reduceFinMk,Fin.reduceEq,
      Nat.reduceLT,if_true,if_false,lie_inverse_scale,auxiliary_lie_inverse_left]
  all_goals simp [auxiliaryLieInverse]
  all_goals ring_nf
  all_goals simp only [inv_inv]

/-- The complete native second clock coefficient acts on every gauge row of the remaining field. -/
theorem actual_native_gauge_schur_second (k : PhysicalMomentum) (r : Fin 217 → ℂ)
    (mu : Fin 4) (a : Fin 12) :
    (nativeSchurClockSecond k*ᵥr) (gaugeRestIndex mu a)=
      if mu=0 then 0 else 2*(lapse : ℂ)*auxiliaryLieReader (fun b => r (gaugeRestIndex mu b)) a := by
  have zero : ((nativePhysicalClockSecond k).submatrix nativeRestIndex nativeRestIndex*ᵥr)
      (gaugeRestIndex mu a)=0 := by
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_eq_zero
    intro j _
    have embed : nativeRestIndex (gaugeRestIndex mu a)=gaugeSlot mu a := by apply Fin.ext;rfl
    simp only [Matrix.submatrix_apply,embed,actual_native_gauge_clock_second_zero,zero_mul]
  unfold nativeSchurClockSecond
  rw [Matrix.sub_mulVec]
  simp only [Pi.sub_apply]
  rw [zero,zero_sub,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  rw [actual_native_rest_time_reader]
  have inverse : nativeAuxiliaryInverseMatrix*ᵥ(nativeAuxiliaryRestClockFirst k*ᵥr)=fun i =>
      if i.1=3 then 2*Complex.I*(lapse : ℂ)*r (gaugeRestIndex 1 i.2) else
      if i.1=4 then 2*Complex.I*(lapse : ℂ)*r (gaugeRestIndex 2 i.2) else
      if i.1=5 then 2*Complex.I*(lapse : ℂ)*r (gaugeRestIndex 3 i.2) else 0 := by
    funext i
    exact actual_native_inverse_time_reader k r i.1 i.2
  rw [inverse]
  fin_cases mu <;> simp only [Fin.reduceFinMk,Fin.reduceEq,if_true,if_false,neg_zero,
    lie_reader_scale]
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring1

/-- The actual EM insertion restricted to the original remaining-field indices. -/
def nativeEMRestInsertion : Matrix (Fin 217) (Fin 4) ℂ :=
  emInsertion.submatrix nativeRestIndex id

private theorem actual_rest_em_projection (r : Fin 217 → ℂ) (mu : Fin 4) :
    (nativeEMRestInsertion.transpose*ᵥr) mu=
      (1/2 : ℂ)*(-r (gaugeRestIndex mu 6)+r (gaugeRestIndex mu 7)-r (gaugeRestIndex mu 11)) := by
  let full : Fin 289 → ℂ := fun j => Fin.addCases r (fun _ : Fin 72 => 0) j
  have same : (emInsertion.transpose*ᵥfull) mu=(nativeEMRestInsertion.transpose*ᵥr) mu := by
    change (∑ j : Fin (217+72),emInsertion j mu*Fin.addCases r (fun _ : Fin 72 => 0) j)=_
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,mul_zero,Finset.sum_const_zero,add_zero]
    rfl
  rw [← same,em_projection_coordinates]
  have embed (a : Fin 12) : gaugeSlot mu a=Fin.castAdd 72 (gaugeRestIndex mu a) := by apply Fin.ext;rfl
  simp only [embed,full,Fin.addCases_left]

/-- The actual EM read of the full native time coefficient retains the complete remaining field. -/
theorem actual_native_em_time_reader (k : PhysicalMomentum) (r : Fin 217 → ℂ) (mu : Fin 4) :
    (nativeEMRestInsertion.transpose*ᵥ(nativeSchurClockSecond k*ᵥr)) mu=
      if mu=0 then 0 else 2*(lapse : ℂ)*(nativeEMRestInsertion.transpose*ᵥr) mu := by
  rw [actual_rest_em_projection,actual_rest_em_projection]
  simp only [actual_native_gauge_schur_second]
  by_cases temporal : mu=0
  · simp only [temporal,if_true,neg_zero,add_zero,sub_zero,mul_zero]
  · simp only [temporal,if_false,auxiliaryLieReader,Fin.reduceEq,if_true,if_false]
    ring1

/-- The time tensor is computed from the actual three-slot EM insertion and the source auxiliary inverse. -/
theorem actual_native_em_time_tensor (k : PhysicalMomentum) :
    nativeEMRestInsertion.transpose*nativeSchurClockSecond k*nativeEMRestInsertion=
      fun mu nu => if mu=0 then 0 else if mu=nu then (3/2 : ℂ)*(lapse : ℂ) else 0 := by
  rw [Matrix.mul_assoc]
  ext mu nu
  change (nativeEMRestInsertion.transpose*ᵥ(nativeSchurClockSecond k*ᵥ
    (fun i => nativeEMRestInsertion i nu))) mu=_
  rw [actual_native_em_time_reader,actual_rest_em_projection]
  have slot (a : Fin 12) : nativeEMRestInsertion (gaugeRestIndex mu a) nu=
      if mu=nu then (rawCoordinates (p286CoordinateEquiv emDirection) a : ℂ) else 0 := by
    change emInsertion (gaugeSlot mu a) nu=_
    by_cases same : mu=nu
    · simp [emInsertion,emGaugeField,Finset.sum_apply,Pi.smul_apply,
        PreparationVacuumGaugeSourceInjection.gauge_gauge_slot,same]
    · simp [emInsertion,emGaugeField,Finset.sum_apply,Pi.smul_apply,
        PreparationVacuumGaugeSourceInjection.gauge_gauge_slot,same]
  simp only [slot,em_original_coordinates,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,
    Pi.single_apply,smul_eq_mul]
  simp only [Fin.reduceEq,if_true,if_false,mul_one,mul_zero,
    sub_zero,zero_sub,add_zero,zero_add,Complex.ofReal_neg,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat]
  by_cases temporal : mu=0
  · simp only [temporal,if_true]
  · simp only [temporal,if_false]
    by_cases same : mu=nu
    · simp only [same,if_true]
      ring1
    · simp only [same,if_false,neg_zero,add_zero,sub_zero,mul_zero]

/-- The same actual EM root consumes the generated time coefficient together with both lower clocks and all Q0 feedback. -/
theorem actual_em_native_principal_coefficient (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (alpha beta mu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n alpha beta)) :
    (nativeEMRestInsertion.transpose*ᵥ(nativeSchurClockZero ((eps^2 : ℝ) • n)*ᵥ
      emRestSlice (actualEMZeroClockMode event eps n beta (s : ℂ)))) mu+
    (sourceFrequency eps s : ℂ)*(nativeEMRestInsertion.transpose*ᵥ
      (nativeSchurClockFirst ((eps^2 : ℝ) • n)*ᵥ
        emRestSlice (actualEMZeroClockMode event eps n beta (s : ℂ)))) mu+
    (sourceFrequency eps s : ℂ)^2*(if mu=0 then 0 else 2*(lapse : ℂ)*
      (nativeEMRestInsertion.transpose*ᵥemRestSlice (actualEMZeroClockMode event eps n beta (s : ℂ))) mu)=
    (nativeEMRestInsertion.transpose*ᵥnativeQuantumSchurForcing (frequencyRay eps s n)
      (zeroClockQuantumResponse event eps s n) (actualEMZeroClockMode event eps n beta (s : ℂ))) mu := by
  have full := actual_em_native_schur_physical_dispersion event eps s n alpha beta balanced finite regular root
  have observed := congrArg (fun v : Fin 217 → ℂ => (nativeEMRestInsertion.transpose*ᵥv) mu) full
  simpa only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.mulVec_add,Matrix.mulVec_smul,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,actual_native_em_time_reader] using observed

end LowEnergy.GaussComposite.ActualDressedEMNativePrincipal
