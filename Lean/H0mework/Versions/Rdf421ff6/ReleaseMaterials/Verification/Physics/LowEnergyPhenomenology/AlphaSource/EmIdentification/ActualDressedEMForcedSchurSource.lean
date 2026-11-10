import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeCouplingConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMOriginalClockResidueBalance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMCorrectedCouplingSource
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open SourcePropagationNativeActionHessian ActualEMAction ActualEMCarrierOwn PhysicalEMGaugeRealization
open CanonicalGradedSpatialSource PreparationCoordinates PreparationVacuumMixedFieldReturn PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockVector ActualDressedZeroClockFrequency
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMNativeSchurClock
open ActualDressedEMNativePrincipal ActualDressedEMNativeMomentum ActualDressedEMNativeCoulomb
open ActualDressedEMPhysicalResidueFlux ActualDressedEMFullPoleFlux
open Polynomial LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

/-- This original elimination reads every full289 force, including all auxiliary quantum forcing. -/
def nativeCompleteForceRead (p : Fin 4 → ℂ) (f : Fin 289 → ℂ) : Fin 217 → ℂ :=
  emRestSlice f-nativeRestAuxiliary p*ᵥ(nativeAuxiliaryInverseMatrix*ᵥemAuxiliarySlice f)

private def wholeIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

private theorem whole_left (i : Fin 217) : wholeIndex (Sum.inl i)=nativeRestIndex i := rfl

private theorem whole_right (i : Fin 6 × Fin 12) : wholeIndex (Sum.inr i)=gaugeAuxiliaryIndex i := by
  apply Fin.ext
  change 217+(i.2.val+12*i.1.val)=217+12*i.1.val+i.2.val
  omega

private theorem whole_sum (f : Fin 289 → ℂ) :
    (∑i,f i)=(∑i : Fin 217,f (nativeRestIndex i))+∑i : Fin 6 × Fin 12,f (gaugeAuxiliaryIndex i) := by
  rw [← wholeIndex.sum_comp f,Fintype.sum_sum_type]
  simp only [whole_left,whole_right]

private theorem native_rest_rows (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) :
    emRestSlice (emOriginalJacobi p*ᵥv)=
      nativeRestRest p*ᵥemRestSlice v+nativeRestAuxiliary p*ᵥemAuxiliarySlice v := by
  funext i
  exact whole_sum (fun j => emOriginalJacobi p (nativeRestIndex i) j*v j)

private theorem native_auxiliary_rows (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) :
    emAuxiliarySlice (emOriginalJacobi p*ᵥv)=nativeAuxiliaryRest p*ᵥemRestSlice v+
      originalGaugeAuxiliaryPencil p*ᵥemAuxiliarySlice v := by
  funext i
  exact whole_sum (fun j => emOriginalJacobi p (gaugeAuxiliaryIndex i) j*v j)

/-- The complete native Schur is a source identity on every full field and every force, before any root or photon hypothesis. -/
theorem actual_native_complete_force_identity (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) :
    nativeSchurMatrix p*ᵥemRestSlice v=nativeCompleteForceRead p (emOriginalJacobi p*ᵥv) := by
  rw [nativeCompleteForceRead,native_rest_rows,native_auxiliary_rows,Matrix.mulVec_add,Matrix.mulVec_add]
  simp only [native_auxiliary_inverse_matrix_action,actual_native_auxiliary_inverse_left,
    nativeSchurMatrix,Matrix.sub_mulVec,← Matrix.mulVec_mulVec]
  abel

private theorem complete_read_add (p : Fin 4 → ℂ) (f g : Fin 289 → ℂ) :
    nativeCompleteForceRead p (f+g)=nativeCompleteForceRead p f+nativeCompleteForceRead p g := by
  have rest : emRestSlice (f+g)=emRestSlice f+emRestSlice g := rfl
  have auxiliary : emAuxiliarySlice (f+g)=emAuxiliarySlice f+emAuxiliarySlice g := rfl
  rw [nativeCompleteForceRead,rest,auxiliary,Matrix.mulVec_add,Matrix.mulVec_add]
  unfold nativeCompleteForceRead
  abel

private theorem complete_read_sub (p : Fin 4 → ℂ) (f g : Fin 289 → ℂ) :
    nativeCompleteForceRead p (f-g)=nativeCompleteForceRead p f-nativeCompleteForceRead p g := by
  have rest : emRestSlice (f-g)=emRestSlice f-emRestSlice g := rfl
  have auxiliary : emAuxiliarySlice (f-g)=emAuxiliarySlice f-emAuxiliarySlice g := rfl
  rw [nativeCompleteForceRead,rest,auxiliary,Matrix.mulVec_sub,Matrix.mulVec_sub]
  unfold nativeCompleteForceRead
  abel

private theorem original_em_auxiliary_zero (i : Fin 6 × Fin 12) (mu : Fin 4) :
    emInsertion (gaugeAuxiliaryIndex i) mu=0 := by
  have ne (a : Fin 12) : gaugeAuxiliaryIndex i≠gaugeSlot mu a := by
    intro same
    have val := congrArg Fin.val same
    change 217+12*i.1.val+i.2.val=9+12*mu.val+a.val at val
    omega
  simp only [emInsertion,emGaugeField,Finset.sum_apply,Pi.smul_apply,gaugeField,Pi.single_apply,
    ne,if_false,smul_zero,Finset.sum_const_zero,Complex.ofReal_zero]

/-- The actual EM observer is the restriction of the same source occurrence to the remaining fields. -/
theorem actual_complete_em_observation (v : Fin 289 → ℂ) :
    nativeEMRestInsertion.transpose*ᵥemRestSlice v=emInsertion.transpose*ᵥv := by
  funext mu
  have split := whole_sum (fun j => emInsertion j mu*v j)
  have zero : (∑j : Fin 6 × Fin 12,emInsertion (gaugeAuxiliaryIndex j) mu*v (gaugeAuxiliaryIndex j))=0 := by
    simp only [original_em_auxiliary_zero,zero_mul,Finset.sum_const_zero]
  rw [zero,add_zero] at split
  exact split.symm

private theorem complete_read_em_input (p : Fin 4 → ℂ) (nu : Fin 4) :
    nativeCompleteForceRead p (fun i => emInsertion i nu)=fun i => nativeEMRestInsertion i nu := by
  have auxiliary : emAuxiliarySlice (fun i => emInsertion i nu)=0 := by
    funext i
    exact original_em_auxiliary_zero i nu
  rw [nativeCompleteForceRead,auxiliary,Matrix.mulVec_zero,Matrix.mulVec_zero,sub_zero]
  rfl

/-- The correction is generated by the actual Q response and native background/lower operator, with no difference-of-couplings definition. -/
def nativeCompleteCorrection (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) : Fin 217 → ℂ :=
  nativeCompleteForceRead p (Q*ᵥv)-nativeSchurMatrix 0*ᵥemRestSlice v-
    nativeMomentumLower p*ᵥemRestSlice v

/-- The full source principal consumes both external forcing and the generated complete correction. -/
theorem actual_native_forced_principal (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) :
    nativeEMMomentumMatrix p*ᵥ(emInsertion.transpose*ᵥv)=
      nativeEMRestInsertion.transpose*ᵥnativeCompleteForceRead p ((emOriginalJacobi p-Q)*ᵥv)+
      nativeEMRestInsertion.transpose*ᵥnativeCompleteCorrection p Q v := by
  have principal : nativeMomentumPrincipal p*ᵥemRestSlice v=
      nativeSchurMatrix p*ᵥemRestSlice v-nativeSchurMatrix 0*ᵥemRestSlice v-
        nativeMomentumLower p*ᵥemRestSlice v := by
    rw [actual_native_momentum_decomposition]
    simp only [Matrix.add_mulVec]
    abel
  rw [← actual_complete_em_observation,← actual_native_em_momentum_principal,
    principal,actual_native_complete_force_identity]
  simp only [Matrix.sub_mulVec,complete_read_sub,nativeCompleteCorrection,Matrix.mulVec_sub]
  abel

private theorem evaluated_column_equation {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ[X]) (V : ι → ℂ[X]) (D d : ℂ[X]) (f : ι → ℂ) (a : ℂ)
    (paid : H*ᵥV=D • (d • fun i => C (f i))) :
    H.map (Polynomial.eval a)*ᵥ(fun i => (V i).eval a)=(D.eval a*d.eval a) • f := by
  funext i
  have value := congrArg (Polynomial.eval a) (congrFun paid i)
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
    eval_finsetSum,eval_mul,eval_C,mul_assoc] using value

private theorem divided_forcing {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (v f : ι → ℂ) (D d : ℂ) (Dne : D≠0) (dne : d≠0)
    (paid : H*ᵥv=(D*d) • f) :
    (fun i j => H i j/d)*ᵥ(fun i => v i/D)=f := by
  funext i
  have value := congrFun paid i
  change (∑j,H i j*v j)=(D*d)*f i at value
  have quotient : (∑j,H i j/d*(v j/D))=(∑j,H i j*v j)/(D*d) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [Dne,dne]
  change (∑j,H i j/d*(v j/D))=f i
  rw [quotient,value,mul_div_cancel_left₀ _ (mul_ne_zero Dne dne)]

/-- The original full289 adjugate forcing column generates the corrected equation before EM compression. -/
theorem actual_corrected_forced_em_column (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (dRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (DRegular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0) :
    (emOriginalJacobi (frequencyRay eps s n)-zeroClockQuantumResponse event eps s n)*ᵥ
      zeroClockEMColumnRead event eps s n nu=(fun i => emInsertion i nu) := by
  have value := evaluated_column_equation _ _ _ _ _ (s : ℂ)
    (actual_zero_clock_em_threshold_equation event eps n nu balanced finite)
  have read : zeroClockEMColumnRead event eps s n nu=
      (fun i => (zeroClockEMColumn event eps n nu i).eval (s : ℂ)/
        (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)) := by
    funext i
    exact reduced_read_at_regular _ _ _ DRegular
  rw [read,← actual_zero_clock_threshold_quantum event eps s n dRegular]
  exact divided_forcing _ _ _ _ _ DRegular dRegular value

/-- Every actual corrected EM forcing column now consumes the explicit full quantum/background/lower correction through the original principal. -/
theorem actual_corrected_em_principal_source (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (dRegular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (DRegular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0) :
    nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n)
      (emInsertion.transpose*ᵥzeroClockEMColumnRead event eps s n nu)=
      ((3/4 : ℂ) • Pi.single nu 1)+
      nativeEMRestInsertion.transpose*ᵥnativeCompleteCorrection (frequencyRay eps s n)
        (zeroClockQuantumResponse event eps s n) (zeroClockEMColumnRead event eps s n nu) := by
  have source := actual_native_forced_principal (frequencyRay eps s n)
    (zeroClockQuantumResponse event eps s n) (zeroClockEMColumnRead event eps s n nu)
  rw [actual_corrected_forced_em_column event eps s n nu balanced finite dRegular DRegular,
    complete_read_em_input] at source
  have gram : nativeEMRestInsertion.transpose*ᵥ(fun i => nativeEMRestInsertion i nu)=
      (3/4 : ℂ) • Pi.single nu 1 := by
    have paid := actual_native_rest_coordinate_gram
    have column := congrArg (fun T : Matrix (Fin 4) (Fin 4) ℂ => fun mu => T mu nu) paid
    funext mu
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,
      Pi.smul_apply,smul_eq_mul,Pi.single_apply,Matrix.mulVec,dotProduct] using congrFun column mu
  rw [gram] at source
  have physical : nativeEMMomentumMatrix (frequencyRay eps s n)*ᵥ
      (emInsertion.transpose*ᵥzeroClockEMColumnRead event eps s n nu)=
      nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n)
        (emInsertion.transpose*ᵥzeroClockEMColumnRead event eps s n nu) := by
    rw [← actual_physical_frequency_ray,actual_native_physical_em_principal]
  rw [physical] at source
  exact source

end LowEnergy.GaussComposite.ActualDressedEMCorrectedCouplingSource
