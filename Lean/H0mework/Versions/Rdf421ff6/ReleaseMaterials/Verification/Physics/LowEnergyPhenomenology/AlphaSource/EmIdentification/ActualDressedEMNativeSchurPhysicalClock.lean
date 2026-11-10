import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMAlgebraicAuxiliaryJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeSchurClock
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet
open ActualEMAction ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback
open ActualDressedEMClockDispersion ActualDressedFullCoulomb
open ActualDressedZeroClockVector ActualDressedEMZeroClockColumns ActualDressedZeroClockFrequency
open ActualDressedEMQuantumThreshold LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

/-- This is the complete original native Schur matrix, before the retained quantum forcing. -/
def nativeSchurMatrix (p : Fin 4 → ℂ) : Matrix (Fin 217) (Fin 217) ℂ :=
  nativeRestRest p-nativeRestAuxiliary p*nativeAuxiliaryInverseMatrix*nativeAuxiliaryRest p

theorem actual_native_schur_matrix_action (p : Fin 4 → ℂ) (r : Fin 217 → ℂ) :
    nativeSchurMatrix p*ᵥr=nativeSchurWave p r := by
  simp only [nativeSchurMatrix,nativeSchurWave,Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec,native_auxiliary_inverse_matrix_action]

def nativeAuxiliaryRestClockFirst (k : PhysicalMomentum) : Matrix (Fin 6 × Fin 12) (Fin 217) ℂ :=
  nativeAuxiliaryRest (physicalFrequencyMomentum 1 k)-nativeAuxiliaryRest (physicalFrequencyMomentum 0 k)

def nativeRestAuxiliaryClockFirst (k : PhysicalMomentum) : Matrix (Fin 217) (Fin 6 × Fin 12) ℂ :=
  nativeRestAuxiliary (physicalFrequencyMomentum 1 k)-nativeRestAuxiliary (physicalFrequencyMomentum 0 k)

def nativeSchurClockZero (k : PhysicalMomentum) : Matrix (Fin 217) (Fin 217) ℂ :=
  nativeSchurMatrix (physicalFrequencyMomentum 0 k)

def nativeSchurClockFirst (k : PhysicalMomentum) : Matrix (Fin 217) (Fin 217) ℂ :=
  (nativePhysicalClockFirst k).submatrix nativeRestIndex nativeRestIndex-
    (nativeRestAuxiliaryClockFirst k*nativeAuxiliaryInverseMatrix*
      nativeAuxiliaryRest (physicalFrequencyMomentum 0 k)+
    nativeRestAuxiliary (physicalFrequencyMomentum 0 k)*nativeAuxiliaryInverseMatrix*
      nativeAuxiliaryRestClockFirst k)

def nativeSchurClockSecond (k : PhysicalMomentum) : Matrix (Fin 217) (Fin 217) ℂ :=
  (nativePhysicalClockSecond k).submatrix nativeRestIndex nativeRestIndex-
    nativeRestAuxiliaryClockFirst k*nativeAuxiliaryInverseMatrix*nativeAuxiliaryRestClockFirst k

private theorem auxiliary_rest_clock_affine (omega : ℝ) (k : PhysicalMomentum) :
    nativeAuxiliaryRest (physicalFrequencyMomentum omega k)=
      nativeAuxiliaryRest (physicalFrequencyMomentum 0 k)+(omega : ℂ) • nativeAuxiliaryRestClockFirst k := by
  ext i j
  have high : 217 ≤ (gaugeAuxiliaryIndex i).val := by dsimp only [gaugeAuxiliaryIndex,gaugeBSlot];omega
  exact actual_native_auxiliary_clock_affine omega k (gaugeAuxiliaryIndex i) (nativeRestIndex j) (Or.inl high)

private theorem rest_auxiliary_clock_affine (omega : ℝ) (k : PhysicalMomentum) :
    nativeRestAuxiliary (physicalFrequencyMomentum omega k)=
      nativeRestAuxiliary (physicalFrequencyMomentum 0 k)+(omega : ℂ) • nativeRestAuxiliaryClockFirst k := by
  ext i j
  have high : 217 ≤ (gaugeAuxiliaryIndex j).val := by dsimp only [gaugeAuxiliaryIndex,gaugeBSlot];omega
  exact actual_native_auxiliary_clock_affine omega k (nativeRestIndex i) (gaugeAuxiliaryIndex j) (Or.inr high)

private theorem rest_rest_clock_quadratic (omega : ℝ) (k : PhysicalMomentum) :
    nativeRestRest (physicalFrequencyMomentum omega k)=nativeRestRest (physicalFrequencyMomentum 0 k)+
      (omega : ℂ) • (nativePhysicalClockFirst k).submatrix nativeRestIndex nativeRestIndex+
      (omega : ℂ)^2 • (nativePhysicalClockSecond k).submatrix nativeRestIndex nativeRestIndex := by
  ext i j
  change emOriginalJacobi (physicalFrequencyMomentum omega k) (nativeRestIndex i) (nativeRestIndex j)=
    emOriginalJacobi (physicalFrequencyMomentum 0 k) (nativeRestIndex i) (nativeRestIndex j)+
    (omega : ℂ)*nativePhysicalClockFirst k (nativeRestIndex i) (nativeRestIndex j)+
    (omega : ℂ)^2*nativePhysicalClockSecond k (nativeRestIndex i) (nativeRestIndex j)
  simpa only [nativePhysicalClockZero,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] using
    congrFun (congrFun (actual_native_physical_clock_quadratic omega k) (nativeRestIndex i)) (nativeRestIndex j)

private theorem matrix_schur_quadratic {R B : Type*} [Fintype R] [Fintype B]
    (t : ℂ) (A0 A1 A2 : Matrix R R ℂ) (B0 B1 : Matrix R B ℂ)
    (C0 C1 : Matrix B R ℂ) (W : Matrix B B ℂ) :
    (A0+t • A1+t^2 • A2)-(B0+t • B1)*W*(C0+t • C1)=
      (A0-B0*W*C0)+t • (A1-(B1*W*C0+B0*W*C1))+t^2 • (A2-B1*W*C1) := by
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
    smul_add,smul_sub,smul_smul,pow_two]
  abel

/-- Algebraic original auxiliaries make the full remaining-field physical clock exactly quadratic. -/
theorem actual_native_schur_physical_clock (omega : ℝ) (k : PhysicalMomentum) :
    nativeSchurMatrix (physicalFrequencyMomentum omega k)=
      nativeSchurClockZero k+(omega : ℂ) • nativeSchurClockFirst k+
        (omega : ℂ)^2 • nativeSchurClockSecond k := by
  unfold nativeSchurMatrix
  rw [rest_rest_clock_quadratic,rest_auxiliary_clock_affine,auxiliary_rest_clock_affine]
  exact matrix_schur_quadratic _ _ _ _ _ _ _ _ _

/-- The same complete EM root consumes these physical clock coefficients with full Q0_B feedback retained. -/
theorem actual_em_native_schur_physical_dispersion (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (nativeSchurClockZero ((eps^2 : ℝ) • n)+
      (sourceFrequency eps s : ℂ) • nativeSchurClockFirst ((eps^2 : ℝ) • n)+
      (sourceFrequency eps s : ℂ)^2 • nativeSchurClockSecond ((eps^2 : ℝ) • n))*ᵥ
      emRestSlice (actualEMZeroClockMode event eps n nu (s : ℂ))=
    nativeQuantumSchurForcing (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)
      (actualEMZeroClockMode event eps n nu (s : ℂ)) := by
  rw [← actual_native_schur_physical_clock,actual_native_schur_matrix_action,actual_physical_frequency_ray]
  exact actual_em_quantum_auxiliary_schur event eps s n mu nu balanced finite regular root

end LowEnergy.GaussComposite.ActualDressedEMNativeSchurClock
