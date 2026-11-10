import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeMomentumPrincipal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeMomentum
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open SourcePropagationNativeActionHessian ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet ActualDressedFullCoulomb ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedZeroClockFrequency
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualDressedEMClockDispersion
open ActualDressedEMNativeSchurClock ActualDressedEMNativePrincipal ActualEMCarrierOwn
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

/-- Original background and all odd momentum couplings, before their actual EM read. -/
def nativeMomentumLower (p : Fin 4 → ℂ) : Matrix (Fin 217) (Fin 217) ℂ :=
  (1/2 : ℂ) • (nativeRestRest p-nativeRestRest (-p))-
    (nativeRestMomentumFirst p*nativeAuxiliaryInverseMatrix*nativeAuxiliaryRest 0+
      nativeRestAuxiliary 0*nativeAuxiliaryInverseMatrix*nativeAuxiliaryMomentumFirst p)

private theorem matrix_principal_decomposition {R B : Type*} [Fintype R] [Fintype B]
    (A Aneg A0 : Matrix R R ℂ) (Bp B0 : Matrix R B ℂ) (Cp C0 : Matrix B R ℂ) (W : Matrix B B ℂ) :
    A-Bp*W*Cp=(A0-B0*W*C0)+
      ((1/2 : ℂ) • (A-Aneg)-((Bp-B0)*W*C0+B0*W*(Cp-C0)))+
      ((1/2 : ℂ) • (A+Aneg)-A0-(Bp-B0)*W*(Cp-C0)) := by
  simp only [Matrix.sub_mul,Matrix.mul_sub,smul_add,smul_sub]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring1

/-- The complete source native Schur retains its background, lower couplings and full217 principal together. -/
theorem actual_native_momentum_decomposition (p : Fin 4 → ℂ) :
    nativeSchurMatrix p=nativeSchurMatrix 0+nativeMomentumLower p+nativeMomentumPrincipal p := by
  have even : (nativeMomentumEven p).submatrix nativeRestIndex nativeRestIndex=
      (1/2 : ℂ) • (nativeRestRest p+nativeRestRest (-p))-nativeRestRest 0 := by
    ext i j
    rfl
  unfold nativeMomentumLower nativeMomentumPrincipal
  rw [even]
  exact matrix_principal_decomposition (nativeRestRest p) (nativeRestRest (-p)) (nativeRestRest 0)
    (nativeRestAuxiliary p) (nativeRestAuxiliary 0) (nativeAuxiliaryRest p) (nativeAuxiliaryRest 0)
    nativeAuxiliaryInverseMatrix

private theorem matrix_schur_even {R B : Type*} [Fintype R] [Fintype B]
    (A Aneg A0 : Matrix R R ℂ) (B0 B1 : Matrix R B ℂ) (C0 C1 : Matrix B R ℂ) (W : Matrix B B ℂ) :
    (1/2 : ℂ) • ((A-(B0+B1)*W*(C0+C1))+(Aneg-(B0-B1)*W*(C0-C1)))-
      (A0-B0*W*C0)=(1/2 : ℂ) • (A+Aneg)-A0-B1*W*C1 := by
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.sub_mul,Matrix.mul_sub,smul_add,smul_sub]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring1

/-- The complete217 principal is exactly the even part of the original source Schur at opposite momenta. -/
theorem actual_native_schur_even_principal (p : Fin 4 → ℂ) :
    (1/2 : ℂ) • (nativeSchurMatrix p+nativeSchurMatrix (-p))-nativeSchurMatrix 0=
      nativeMomentumPrincipal p := by
  have rbPlus : nativeRestAuxiliary p=nativeRestAuxiliary 0+nativeRestMomentumFirst p := by
    unfold nativeRestMomentumFirst
    abel
  have brPlus : nativeAuxiliaryRest p=nativeAuxiliaryRest 0+nativeAuxiliaryMomentumFirst p := by
    unfold nativeAuxiliaryMomentumFirst
    abel
  have rbMinus : nativeRestAuxiliary (-p)=nativeRestAuxiliary 0-nativeRestMomentumFirst p := by
    have odd := actual_native_rest_momentum_odd p
    unfold nativeRestMomentumFirst at odd
    have paid := eq_add_of_sub_eq odd
    simpa only [nativeRestMomentumFirst,nativeAuxiliaryMomentumFirst,sub_eq_add_neg,add_comm] using paid
  have brMinus : nativeAuxiliaryRest (-p)=nativeAuxiliaryRest 0-nativeAuxiliaryMomentumFirst p := by
    have odd := actual_native_auxiliary_momentum_odd p
    unfold nativeAuxiliaryMomentumFirst at odd
    have paid := eq_add_of_sub_eq odd
    simpa only [nativeRestMomentumFirst,nativeAuxiliaryMomentumFirst,sub_eq_add_neg,add_comm] using paid
  have even : (nativeMomentumEven p).submatrix nativeRestIndex nativeRestIndex=
      (1/2 : ℂ) • (nativeRestRest p+nativeRestRest (-p))-nativeRestRest 0 := by
    ext i j
    rfl
  unfold nativeSchurMatrix nativeMomentumPrincipal
  rw [rbPlus,brPlus,rbMinus,brMinus,even]
  exact matrix_schur_even _ _ _ _ _ _ _ _

private theorem source_auxiliary_inverse_weights :
    (fun pair : Fin 6 => (nativeAuxiliaryWeight pair)⁻¹)=
      ![2*(lapse : ℂ)⁻¹,2*(lapse : ℂ)⁻¹,2*(lapse : ℂ)⁻¹,
        -2*(lapse : ℂ),-2*(lapse : ℂ),-2*(lapse : ℂ)] := by
  funext pair
  fin_cases pair <;> simp only [nativeAuxiliaryWeight,Fin.reduceFinMk,Nat.reduceLT,if_true,if_false]
  all_goals dsimp only [Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals ring_nf
  all_goals simp only [inv_inv]

/-- The original four-component physical principal keeps its temporal constraint and longitudinal terms. -/
def nativePhysicalEMPrincipal (omega : ℝ) (k : PhysicalMomentum) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  let K : Fin 3 → ℂ := fun i => (k i : ℂ)
  let longitudinal := K 0*v 1+K 1*v 2+K 2*v 3
  let square := K 0^2+K 1^2+K 2^2
  ![2*(lapse : ℂ)*(square*v 0+(omega : ℂ)*longitudinal),
    2*(lapse : ℂ)*(omega : ℂ)^2*v 1+2*(lapse : ℂ)*(omega : ℂ)*K 0*v 0-
      2*(lapse : ℂ)⁻¹*(square*v 1-K 0*longitudinal),
    2*(lapse : ℂ)*(omega : ℂ)^2*v 2+2*(lapse : ℂ)*(omega : ℂ)*K 1*v 0-
      2*(lapse : ℂ)⁻¹*(square*v 2-K 1*longitudinal),
    2*(lapse : ℂ)*(omega : ℂ)^2*v 3+2*(lapse : ℂ)*(omega : ℂ)*K 2*v 0-
      2*(lapse : ℂ)⁻¹*(square*v 3-K 2*longitudinal)]

/-- This complete physical symbol is generated from the original six source curl slots and inverse weights. -/
theorem actual_native_physical_em_principal (omega : ℝ) (k : PhysicalMomentum) (v : Fin 4 → ℂ) :
    nativeEMMomentumMatrix (physicalFrequencyMomentum omega k)*ᵥv=nativePhysicalEMPrincipal omega k v := by
  rw [actual_native_em_momentum_matrix_action]
  change nativeMomentumDivergence (physicalFrequencyMomentum omega k)
    ((fun pair : Fin 6 => (nativeAuxiliaryWeight pair)⁻¹)*
      nativeMomentumCurl (physicalFrequencyMomentum omega k) v)=_
  rw [source_auxiliary_inverse_weights]
  have kZero (h : 0<3) : k (⟨0,h⟩ : Fin 3)=k 0 := rfl
  have kOne (h : 1<3) : k (⟨1,h⟩ : Fin 3)=k 1 := rfl
  have kTwo (h : 2<3) : k (⟨2,h⟩ : Fin 3)=k 2 := rfl
  funext mu
  fin_cases mu <;>
    simp only [nativeMomentumDivergence,nativeMomentumCurl,nativePhysicalEMPrincipal,
      Pi.mul_apply,physicalFrequencyMomentum]
  all_goals dsimp only [Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq,kZero,kOne,kTwo]
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring1

/-- The same actual EM root consumes the complete original constrained time/space principal and all corrected forcing. -/
theorem actual_em_native_momentum_equation (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (alpha beta : Fin 4) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n alpha beta)) :
    nativeEMRestInsertion.transpose*ᵥ(nativeSchurMatrix 0*ᵥ
      emRestSlice (actualEMZeroClockMode event eps n beta (s : ℂ)))+
    nativeEMRestInsertion.transpose*ᵥ(nativeMomentumLower (frequencyRay eps s n)*ᵥ
      emRestSlice (actualEMZeroClockMode event eps n beta (s : ℂ)))+
    nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n)
      (nativeEMRestInsertion.transpose*ᵥemRestSlice (actualEMZeroClockMode event eps n beta (s : ℂ)))=
    nativeEMRestInsertion.transpose*ᵥnativeQuantumSchurForcing (frequencyRay eps s n)
      (zeroClockQuantumResponse event eps s n) (actualEMZeroClockMode event eps n beta (s : ℂ)) := by
  have full := actual_em_quantum_auxiliary_schur event eps s n alpha beta balanced finite regular root
  rw [← actual_native_schur_matrix_action,actual_native_momentum_decomposition] at full
  have observed := congrArg (fun v : Fin 217 → ℂ => nativeEMRestInsertion.transpose*ᵥv) full
  simp only [Matrix.add_mulVec,Matrix.mulVec_add,actual_native_em_momentum_principal] at observed
  have physical : nativeEMMomentumMatrix (frequencyRay eps s n)*ᵥ
      (nativeEMRestInsertion.transpose*ᵥemRestSlice (actualEMZeroClockMode event eps n beta (s : ℂ)))=
      nativePhysicalEMPrincipal (sourceFrequency eps s) ((eps^2 : ℝ) • n)
        (nativeEMRestInsertion.transpose*ᵥemRestSlice (actualEMZeroClockMode event eps n beta (s : ℂ))) := by
    rw [← actual_physical_frequency_ray,actual_native_physical_em_principal]
  rw [physical] at observed
  exact observed

end LowEnergy.GaussComposite.ActualDressedEMNativeMomentum
