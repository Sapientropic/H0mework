import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMPairedLeftPole

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMPolePairEnergy
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMClockDispersion ActualDressedEMQuantumThreshold
open ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux ActualDressedEMPhysicalResidueFlux
open ActualDressedEMSourceTransport ActualEMCarrierOwn LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators Topology
attribute [local irreducible] correctedPhysicalClock correctedPhysicalClockJet emPhysicalPairedLeftMode
  emPhysicalPairedLeftDefect emFullPhysicalResidue emPhysicalCorrectedPoleCoefficient
  emPhysicalNormalizedPoleColumnCoefficient emFullColumnPoleOrder emFullAnalyticColumnNumerator
  emColumnDenominatorTail sourceTangentPhysicalSpatialJet actualSourceCoulombTensor

private theorem paired_matrix_read {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) (l v : ι→ℂ) :
    dotProduct l (P*ᵥv)=dotProduct (P.transpose*ᵥl) v := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The analytic column is the original canonical coefficient at the full pole order. -/
def emPairedAnalyticColumn (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (nu : Fin 4) (a : ℂ) : Fin 289→ℂ :=
  fun i => (emFullAnalyticColumnNumerator event eps n nu a i).eval a/(emColumnDenominatorTail event eps n a).eval a

def emPairedClockEnergy (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) : ℂ :=
  dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))
    (correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ))

def emPairedHigherEnergy (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) : ℂ :=
  dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))
    (∑r∈Finset.range (emFullColumnPoleOrder event eps n nu (s : ℂ)-1),
      emPhysicalCorrectedPoleCoefficient event eps n (s : ℂ) (r+2)*ᵥ
        emPhysicalNormalizedPoleColumnCoefficient event eps n nu (s : ℂ)
          (emFullColumnPoleOrder event eps n nu (s : ℂ)-(r+2)))

def emPairedSourceInput (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) : ℂ :=
  dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ)) (fun i => emInsertion i nu)

def emPairedAnalyticClockDebt (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) : ℂ :=
  dotProduct (emPhysicalPairedLeftDefect event eps n mu (s : ℂ)) (emPairedAnalyticColumn event eps n nu (s : ℂ))

/-- The actual paired-left source consumes every pole order and the analytic column in the original physical flux. -/
theorem actual_em_paired_energy_balance (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emPairedClockEnergy event eps s n mu nu+emPairedHigherEnergy event eps s n mu nu=
      emPairedSourceInput event eps s n mu nu+emPairedAnalyticClockDebt event eps s n mu nu := by
  have full := actual_em_original_physical_residue_balance event eps s n mu nu eps_ne balanced finite regular root
  have projected := congrArg (dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))) full
  rw [dotProduct_add,dotProduct_add,paired_matrix_read,
    actual_em_physical_paired_left_defect event eps s n mu nu eps_ne regular root,neg_dotProduct] at projected
  have analytic : emPairedAnalyticColumn event eps n nu (s : ℂ)=
      (fun i => (emFullAnalyticColumnNumerator event eps n nu (s : ℂ) i).eval (s : ℂ)/
        (emColumnDenominatorTail event eps n (s : ℂ)).eval (s : ℂ)) := rfl
  rw [←analytic] at projected
  have priced : -emPairedAnalyticClockDebt event eps s n mu nu+emPairedClockEnergy event eps s n mu nu+
      emPairedHigherEnergy event eps s n mu nu=emPairedSourceInput event eps s n mu nu := by
    simpa only [emPairedAnalyticClockDebt,emPairedClockEnergy,emPairedHigherEnergy,
      emPairedSourceInput] using projected
  linear_combination priced

private theorem physical_coefficient_factor {ι : Type*} [Fintype ι]
    (P V : ι→ℕ→ℂ) (beta : ℂ) (q k : ℕ) :
    (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
      (P j p.1/beta^p.1)*(beta^q*V j p.2/beta^p.2))=
      (beta^q/beta^k)*(∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,P j p.1*V j p.2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have degree := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [div_mul_div_comm,←pow_add,degree]
  ring

/-- All lower physical pole-chain coefficients are generated by the same full source series, including Jordan/helicity degeneracy. -/
theorem actual_em_physical_lower_pole_chain (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval a≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (k : ℕ) (lower : k<emFullColumnPoleOrder event eps n nu a) (i : Fin 289) :
    (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
      emPhysicalCorrectedPoleCoefficient event eps n a p.1 i j*
        emPhysicalNormalizedPoleColumnCoefficient event eps n nu a p.2 j)=0 := by
  have source := congrArg (PowerSeries.coeff k)
    (congrFun (actual_em_normalized_full_pole_series event eps n mu nu a balanced finite regular root) i)
  have forced : PowerSeries.coeff k ((PowerSeries.X : PowerSeries ℂ)^emFullColumnPoleOrder event eps n nu a*
      PowerSeries.C (emInsertion i nu))=0 := by
    rw [PowerSeries.coeff_X_pow_mul',if_neg (Nat.not_le_of_lt lower)]
  simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,map_sum] at source
  rw [forced] at source
  have raw : (∑j,∑p∈Finset.HasAntidiagonal.antidiagonal k,
      emCorrectedPoleCoefficient event eps n a p.1 i j*emNormalizedPoleColumnCoefficient event eps n nu a p.2 j)=0 := by
    simpa only [PowerSeries.coeff_mul,emCorrectedPoleCoefficient,
      emNormalizedPoleColumnCoefficient] using source
  have physical := physical_coefficient_factor
    (fun j r => emCorrectedPoleCoefficient event eps n a r i j)
    (fun j r => emNormalizedPoleColumnCoefficient event eps n nu a r j)
    ((eps^2 : ℝ) : ℂ) (emFullColumnPoleOrder event eps n nu a) k
  rw [raw,mul_zero] at physical
  simpa only [emPhysicalCorrectedPoleCoefficient,emPhysicalNormalizedPoleColumnCoefficient] using physical

/-- Physical spatial energy is read from the already-generated complete corrected spatial jet in the same paired mode. -/
def emPairedSpatialEnergy (event : DressedEvent) (eps s : ℝ) (n delta : PhysicalMomentum) (mu nu : Fin 4) : ℂ :=
  -(eps^2 : ℂ)⁻¹*dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))
    (sourceTangentPhysicalSpatialJet event eps (sourceFrequency eps s) n delta*ᵥ
      emFullPhysicalResidue event eps n nu (s : ℂ))

def emEnergyNormalizedResidue (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4) : Fin 289→ℂ :=
  (emPairedClockEnergy event eps s n mu nu)⁻¹ • emFullPhysicalResidue event eps n nu (s : ℂ)

private theorem paired_operator_derivative (M : ℝ→Matrix (Fin 289) (Fin 289) ℂ)
    (M' : Matrix (Fin 289) (Fin 289) ℂ) (x : ℝ) (l v : Fin 289→ℂ) (source : HasDerivAt M M' x) :
    HasDerivAt (fun t : ℝ => dotProduct l (M t*ᵥv)) (dotProduct l (M'*ᵥv)) x := by
  simp only [Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp source i)) j).mul_const (v j)

/-- The energy read is the actual physical frequency derivative in the source-generated pair, held at that pole. -/
theorem actual_em_paired_clock_derivative (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0) :
    HasDerivAt (fun omega : ℝ => dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))
      (correctedPhysicalClock event eps omega n*ᵥemFullPhysicalResidue event eps n nu (s : ℂ)))
      (emPairedClockEnergy event eps s n mu nu) (sourceFrequency eps s) := by
  have point : sourceFrequency eps s/eps^2=s := by
    unfold sourceFrequency
    exact mul_div_cancel_left₀ s (pow_ne_zero 2 eps_ne)
  exact paired_operator_derivative _ _ _ _ _
    (actual_corrected_physical_clock_derivative event eps (sourceFrequency eps s) n eps_ne
      (by simpa only [point] using regular))

/-- Both physical derivative units are consumed; n-tangent carries the original eps² physical spatial factor. -/
theorem actual_em_paired_spatial_derivative (event : DressedEvent) (eps s : ℝ) (n delta : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0)
    (regular : sourceTangentRead (sourceTangentThresholdClearing event eps n delta) 0
      ((sourceFrequency eps s/eps^2 : ℝ) : ℂ)≠0) :
    HasDerivAt (fun t : ℝ => dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))
      (correctedPhysicalClock event eps (sourceFrequency eps s) (sourceTangentMomentum n delta t)*ᵥ
        emFullPhysicalResidue event eps n nu (s : ℂ)))
      (-(eps^2 : ℂ)*emPairedSpatialEnergy event eps s n delta mu nu) 0 := by
  have generated := paired_operator_derivative _ _ _
    (emPhysicalPairedLeftMode event eps n mu (s : ℂ)) (emFullPhysicalResidue event eps n nu (s : ℂ))
    (actual_corrected_physical_spatial_derivative event eps (sourceFrequency eps s) n delta eps_ne regular)
  have beta : (eps^2 : ℂ)≠0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr eps_ne)
  have factor : dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))
      (sourceTangentPhysicalSpatialJet event eps (sourceFrequency eps s) n delta*ᵥ
        emFullPhysicalResidue event eps n nu (s : ℂ))=
      -(eps^2 : ℂ)*emPairedSpatialEnergy event eps s n delta mu nu := by
    unfold emPairedSpatialEnergy
    simp only [neg_mul,mul_neg,neg_neg,←mul_assoc,mul_inv_cancel₀ beta,one_mul]
  rw [factor] at generated
  exact generated

/-- A unit clock read is generated on its actual nonzero energy chart, rather than imported as a residue premise. -/
theorem actual_em_source_normalized_clock_read (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (energy : emPairedClockEnergy event eps s n mu nu≠0) :
    dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))
      (correctedPhysicalClockJet event eps (sourceFrequency eps s) n*ᵥ
        emEnergyNormalizedResidue event eps s n mu nu)=1 := by
  rw [emEnergyNormalizedResidue,Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul]
  exact inv_mul_cancel₀ energy

/-- This is the complete source-normalized spatial flux read; identifying a propagation branch still consumes the pole chain. -/
theorem actual_em_source_normalized_spatial_read (event : DressedEvent) (eps s : ℝ) (n delta : PhysicalMomentum) (mu nu : Fin 4) :
    -(eps^2 : ℂ)⁻¹*dotProduct (emPhysicalPairedLeftMode event eps n mu (s : ℂ))
      (sourceTangentPhysicalSpatialJet event eps (sourceFrequency eps s) n delta*ᵥ
        emEnergyNormalizedResidue event eps s n mu nu)=
      emPairedSpatialEnergy event eps s n delta mu nu/emPairedClockEnergy event eps s n mu nu := by
  rw [emEnergyNormalizedResidue,Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul]
  unfold emPairedSpatialEnergy
  ring

/-- Nondegenerate and degenerate energy charts preserve the higher and analytic source terms. -/
theorem actual_em_source_energy_disposition (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (mu nu : Fin 4)
    (eps_ne : eps≠0) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (root : (s : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    (emPairedClockEnergy event eps s n mu nu≠0 ∧
      1+emPairedHigherEnergy event eps s n mu nu/emPairedClockEnergy event eps s n mu nu=
        (emPairedSourceInput event eps s n mu nu+emPairedAnalyticClockDebt event eps s n mu nu)/
          emPairedClockEnergy event eps s n mu nu) ∨
    (emPairedClockEnergy event eps s n mu nu=0 ∧
      emPairedHigherEnergy event eps s n mu nu=
        emPairedSourceInput event eps s n mu nu+emPairedAnalyticClockDebt event eps s n mu nu) := by
  have source := actual_em_paired_energy_balance event eps s n mu nu eps_ne balanced finite regular root
  by_cases energy : emPairedClockEnergy event eps s n mu nu=0
  · exact Or.inr ⟨energy,by simpa only [energy,zero_add] using source⟩
  · apply Or.inl
    refine ⟨energy,?_⟩
    have price := congrArg (fun z : ℂ => z/emPairedClockEnergy event eps s n mu nu) source
    simpa only [add_div,div_self energy] using price

/-- The held actual pole energy unit carries the entire Noether four-tensor, including its angular dependence. -/
def emHeldEnergyUnitTensor (event : DressedEvent) (eps s : ℝ) (poleMomentum n : PhysicalMomentum) (mu nu : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (emPairedClockEnergy event eps s poleMomentum mu nu)⁻¹ • actualSourceCoulombTensor event n

theorem actual_em_held_energy_unit_tensor_derivative (event : DressedEvent) (eps s : ℝ)
    (poleMomentum n delta : PhysicalMomentum) (mu nu : Fin 4)
    (_energy : emPairedClockEnergy event eps s poleMomentum mu nu≠0)
    (regular : ActualDressedAngularSpherePrice.directionLeadingRead event n≠0) :
    HasDerivAt (fun t : ℝ => emHeldEnergyUnitTensor event eps s poleMomentum
      (sourceTangentMomentum n delta t) mu nu)
      ((emPairedClockEnergy event eps s poleMomentum mu nu)⁻¹ • sourceCoulombTensorSpatialJet event n delta) 0 := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have entry := (hasDerivAt_pi.mp (hasDerivAt_pi.mp
    (actual_source_coulomb_tensor_spatial_derivative event n delta regular) i)) j
  simpa only [emHeldEnergyUnitTensor,Matrix.smul_apply,smul_eq_mul] using
    entry.const_mul (emPairedClockEnergy event eps s poleMomentum mu nu)⁻¹

/-- The actual nonzero energy unit preserves, rather than eliminates, the source tensor gradient responsibility. -/
theorem actual_em_energy_unit_gradient_condition (event : DressedEvent) (eps s : ℝ)
    (poleMomentum n delta : PhysicalMomentum) (mu nu : Fin 4)
    (energy : emPairedClockEnergy event eps s poleMomentum mu nu≠0) :
    ((emPairedClockEnergy event eps s poleMomentum mu nu)⁻¹ • sourceCoulombTensorSpatialJet event n delta)=0 ↔
      sourceCoulombTensorSpatialJet event n delta=0 := by
  simp only [smul_eq_zero,inv_eq_zero,energy,false_or]

end LowEnergy.GaussComposite.ActualDressedEMPolePairEnergy
