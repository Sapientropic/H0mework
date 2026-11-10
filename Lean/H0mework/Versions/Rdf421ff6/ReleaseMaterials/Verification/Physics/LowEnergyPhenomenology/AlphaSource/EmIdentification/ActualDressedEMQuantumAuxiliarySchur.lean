import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeAuxiliaryInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
open SourcePropagationNativeActionHessian ActualEMAction
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockVector ActualDressedEMZeroClockColumns
open ActualDressedZeroClockFrequency ActualDressedEMQuantumThreshold
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators
attribute [local irreducible] emOriginalJacobi

def nativeRestIndex (i : Fin 217) : Fin 289 := Fin.castAdd 72 i

def emRestSlice (v : Fin 289 → ℂ) : Fin 217 → ℂ := fun i => v (nativeRestIndex i)

def emAuxiliarySlice (v : Fin 289 → ℂ) : (Fin 6 × Fin 12) → ℂ :=
  fun i => v (gaugeAuxiliaryIndex i)

def nativeRestRest (p : Fin 4 → ℂ) : Matrix (Fin 217) (Fin 217) ℂ :=
  (emOriginalJacobi p).submatrix nativeRestIndex nativeRestIndex

def nativeRestAuxiliary (p : Fin 4 → ℂ) : Matrix (Fin 217) (Fin 6 × Fin 12) ℂ :=
  (emOriginalJacobi p).submatrix nativeRestIndex gaugeAuxiliaryIndex

def nativeAuxiliaryRest (p : Fin 4 → ℂ) : Matrix (Fin 6 × Fin 12) (Fin 217) ℂ :=
  (emOriginalJacobi p).submatrix gaugeAuxiliaryIndex nativeRestIndex

/-- The remaining 217 original fields retain every native coupling after eliminating the 72 auxiliaries. -/
def nativeSchurWave (p : Fin 4 → ℂ) (r : Fin 217 → ℂ) : Fin 217 → ℂ :=
  nativeRestRest p*ᵥr-nativeRestAuxiliary p*ᵥnativeAuxiliaryInverse (nativeAuxiliaryRest p*ᵥr)

/-- Quantum auxiliary forcing remains a complete full-field response before the same elimination. -/
def nativeQuantumSchurForcing (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) : Fin 217 → ℂ :=
  emRestSlice (Q*ᵥv)-nativeRestAuxiliary p*ᵥnativeAuxiliaryInverse (emAuxiliarySlice (Q*ᵥv))

private def wholeFieldIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

private theorem whole_field_left (i : Fin 217) : wholeFieldIndex (Sum.inl i)=nativeRestIndex i := rfl

private theorem whole_field_right (i : Fin 6 × Fin 12) :
    wholeFieldIndex (Sum.inr i)=gaugeAuxiliaryIndex i := by
  apply Fin.ext
  change 217+(i.2.val+12*i.1.val)=217+12*i.1.val+i.2.val
  omega

private theorem whole_field_sum (f : Fin 289 → ℂ) :
    ∑ i, f i=(∑ i : Fin 217, f (nativeRestIndex i))+
      ∑ i : Fin 6 × Fin 12, f (gaugeAuxiliaryIndex i) := by
  rw [← wholeFieldIndex.sum_comp f,Fintype.sum_sum_type]
  simp only [whole_field_left,whole_field_right]

private theorem full_row_split (J : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 289 → ℂ)
    (i : Fin 289) :
    (J*ᵥv) i=((J.submatrix (fun _ : Unit => i) nativeRestIndex)*ᵥemRestSlice v) ()+
      ((J.submatrix (fun _ : Unit => i) gaugeAuxiliaryIndex)*ᵥemAuxiliarySlice v) () := by
  exact whole_field_sum (fun j => J i j*v j)

private theorem original_auxiliary_rows (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) :
    emAuxiliarySlice (emOriginalJacobi p*ᵥv)=
      nativeAuxiliaryRest p*ᵥemRestSlice v+originalGaugeAuxiliaryPencil p*ᵥemAuxiliarySlice v := by
  funext i
  exact full_row_split (emOriginalJacobi p) v (gaugeAuxiliaryIndex i)

private theorem original_rest_rows (p : Fin 4 → ℂ) (v : Fin 289 → ℂ) :
    emRestSlice (emOriginalJacobi p*ᵥv)=
      nativeRestRest p*ᵥemRestSlice v+nativeRestAuxiliary p*ᵥemAuxiliarySlice v := by
  funext i
  exact full_row_split (emOriginalJacobi p) v (nativeRestIndex i)

private theorem forced_auxiliary (p : Fin 4 → ℂ) (v q : Fin 289 → ℂ)
    (balance : emOriginalJacobi p*ᵥv=q) :
    emAuxiliarySlice v=nativeAuxiliaryInverse
      (emAuxiliarySlice q-nativeAuxiliaryRest p*ᵥemRestSlice v) := by
  have observed := congrArg emAuxiliarySlice balance
  rw [original_auxiliary_rows] at observed
  have forced : originalGaugeAuxiliaryPencil p*ᵥemAuxiliarySlice v=
      emAuxiliarySlice q-nativeAuxiliaryRest p*ᵥemRestSlice v := by
    exact eq_sub_of_add_eq (by simpa only [add_comm] using observed)
  have inverse := congrArg nativeAuxiliaryInverse forced
  rw [actual_native_auxiliary_inverse_left] at inverse
  exact inverse

private theorem forced_schur (p : Fin 4 → ℂ) (Q : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289 → ℂ) (balance : emOriginalJacobi p*ᵥv=Q*ᵥv) :
    nativeSchurWave p (emRestSlice v)=nativeQuantumSchurForcing p Q v := by
  have observed := congrArg emRestSlice balance
  rw [original_rest_rows,forced_auxiliary p v (Q*ᵥv) balance,
    native_auxiliary_inverse_sub,Matrix.mulVec_sub] at observed
  unfold nativeSchurWave nativeQuantumSchurForcing
  apply eq_sub_of_add_eq
  calc
    _=nativeRestRest p*ᵥemRestSlice v+
        (nativeRestAuxiliary p*ᵥnativeAuxiliaryInverse (emAuxiliarySlice (Q*ᵥv))-
          nativeRestAuxiliary p*ᵥnativeAuxiliaryInverse (nativeAuxiliaryRest p*ᵥemRestSlice v)) := by abel
    _=emRestSlice (Q*ᵥv) := observed

/-- The original EM root generates its auxiliary constitutive field with complete Q0_B feedback. -/
theorem actual_em_quantum_auxiliary_constitutive (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emAuxiliarySlice (actualEMZeroClockMode event eps n nu (s : ℂ))=
      nativeAuxiliaryInverse
        (emAuxiliarySlice (zeroClockQuantumResponse event eps s n*ᵥ
          actualEMZeroClockMode event eps n nu (s : ℂ))-
        nativeAuxiliaryRest (frequencyRay eps s n)*ᵥ
          emRestSlice (actualEMZeroClockMode event eps n nu (s : ℂ))) := by
  exact forced_auxiliary _ _ _
    (actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root)

/-- The same complete EM mode obeys the native Schur equation with all quantum mixing retained. -/
theorem actual_em_quantum_auxiliary_schur (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    nativeSchurWave (frequencyRay eps s n)
        (emRestSlice (actualEMZeroClockMode event eps n nu (s : ℂ)))=
      nativeQuantumSchurForcing (frequencyRay eps s n) (zeroClockQuantumResponse event eps s n)
        (actualEMZeroClockMode event eps n nu (s : ℂ)) := by
  exact forced_schur _ _ _
    (actual_zero_clock_em_original_balance event eps s n mu nu balanced finite regular root)

end LowEnergy.GaussComposite.ActualDressedEMNativeAuxiliary
