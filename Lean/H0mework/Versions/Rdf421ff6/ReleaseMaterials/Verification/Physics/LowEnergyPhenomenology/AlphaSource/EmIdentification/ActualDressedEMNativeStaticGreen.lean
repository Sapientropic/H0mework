import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeMomentumConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherCoulombCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeCoulomb
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedEMNativeMomentum ActualDressedEMNativePrincipal ActualDressedEMNativeAuxiliary
open ActualDressedEMNativeSchurClock ActualDressedEMQuantumThreshold ActualDressedFullCoulomb
open ActualDressedEMZeroClockColumns ActualDressedZeroClockVector ActualDressedZeroClockFrequency
open ActualDressedEMClockDispersion ActualEMCarrierOwn ActualEMCurrentSplit
open ActualDressedNoetherCoulombUnit ActualCompositeFieldCurrent
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators

private theorem source_lapse_ne : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'

/-- The longitudinal contraction uses the same physical momentum as the original literal jets. -/
def nativeSpatialContraction (k : PhysicalMomentum) (v : Fin 4 → ℂ) : ℂ :=
  (k 0 : ℂ)*v 1+(k 1 : ℂ)*v 2+(k 2 : ℂ)*v 3

/-- Static Gauss and transverse response; the longitudinal gauge null direction is retained. -/
def nativeStaticGreen (k : PhysicalMomentum) (f : Fin 4 → ℂ) : Fin 4 → ℂ :=
  let q := (spatialSquare k : ℂ)
  ![f 0/(2*(lapse : ℂ)*q),
    -(lapse : ℂ)/(2*q)*(f 1-(k 0 : ℂ)*nativeSpatialContraction k f/q),
    -(lapse : ℂ)/(2*q)*(f 2-(k 1 : ℂ)*nativeSpatialContraction k f/q),
    -(lapse : ℂ)/(2*q)*(f 3-(k 2 : ℂ)*nativeSpatialContraction k f/q)]

def nativeStaticConstraintProjection (k : PhysicalMomentum) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![v 0,v 1-(k 0 : ℂ)*nativeSpatialContraction k v/(spatialSquare k : ℂ),
    v 2-(k 1 : ℂ)*nativeSpatialContraction k v/(spatialSquare k : ℂ),
    v 3-(k 2 : ℂ)*nativeSpatialContraction k v/(spatialSquare k : ℂ)]

private theorem source_square (k : PhysicalMomentum) :
    (spatialSquare k : ℂ)=(k 0 : ℂ)^2+(k 1 : ℂ)^2+(k 2 : ℂ)^2 := by
  simp only [spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]

/-- The inverse is generated from all four original principal equations, rather than an assumed scalar Coulomb equation. -/
theorem actual_native_static_green_right (k : PhysicalMomentum) (nonzero : spatialSquare k≠0)
    (f : Fin 4 → ℂ) :
    nativeEMMomentumMatrix (physicalFrequencyMomentum 0 k)*ᵥnativeStaticGreen k f=
      nativeStaticConstraintProjection k f := by
  rw [actual_native_physical_em_principal]
  have q : (spatialSquare k : ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  have ln := source_lapse_ne
  funext mu
  fin_cases mu <;> simp only [nativePhysicalEMPrincipal,nativeStaticGreen,nativeStaticConstraintProjection,
    nativeSpatialContraction,Complex.ofReal_zero,mul_zero,zero_mul,add_zero]
  all_goals dsimp only [Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals generalize hl : (lapse : ℂ)=L at ln ⊢
  all_goals rw [← source_square]
  all_goals field_simp [q,ln]
  all_goals try simp only [source_square,zero_pow (by decide : 2≠0),mul_zero]
  all_goals ring1

/-- The other composition recovers the same constraint projector, leaving the physical longitudinal kernel explicit. -/
theorem actual_native_static_green_left (k : PhysicalMomentum) (nonzero : spatialSquare k≠0)
    (v : Fin 4 → ℂ) :
    nativeStaticGreen k (nativeEMMomentumMatrix (physicalFrequencyMomentum 0 k)*ᵥv)=
      nativeStaticConstraintProjection k v := by
  rw [actual_native_physical_em_principal]
  have q : (spatialSquare k : ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  have ln := source_lapse_ne
  funext mu
  fin_cases mu <;> simp only [nativePhysicalEMPrincipal,nativeStaticGreen,nativeStaticConstraintProjection,
    nativeSpatialContraction,Complex.ofReal_zero,mul_zero,zero_mul,add_zero]
  all_goals dsimp only [Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals generalize hl : (lapse : ℂ)=L at ln ⊢
  all_goals rw [← source_square]
  all_goals field_simp [q,ln]
  all_goals try simp only [source_square,zero_pow (by decide : 2≠0),mul_zero]
  all_goals ring1

/-- This is the original temporal source read of every complete remaining-field principal input. -/
theorem actual_native_static_temporal_reader (k : PhysicalMomentum) (r : Fin 217 → ℂ) :
    (nativeEMRestInsertion.transpose*ᵥ(nativeMomentumPrincipal (physicalFrequencyMomentum 0 k)*ᵥr)) 0=
      2*(lapse : ℂ)*(spatialSquare k : ℂ)*(nativeEMRestInsertion.transpose*ᵥr) 0 := by
  rw [actual_native_em_momentum_principal,actual_native_physical_em_principal]
  simp only [nativePhysicalEMPrincipal,Complex.ofReal_zero,mul_zero,Matrix.cons_val_zero]
  rw [source_square]
  ring1

/-- The full source Schur can be solved in its temporal native chart without dropping a single lower/background term. -/
theorem actual_native_static_temporal_solve (k : PhysicalMomentum) (nonzero : spatialSquare k≠0)
    (r : Fin 217 → ℂ) :
    (nativeEMRestInsertion.transpose*ᵥr) 0=
      ((nativeEMRestInsertion.transpose*ᵥ(nativeSchurMatrix (physicalFrequencyMomentum 0 k)*ᵥr)) 0-
        (nativeEMRestInsertion.transpose*ᵥ(nativeSchurMatrix 0*ᵥr)) 0-
        (nativeEMRestInsertion.transpose*ᵥ(nativeMomentumLower (physicalFrequencyMomentum 0 k)*ᵥr)) 0)/
          (2*(lapse : ℂ)*(spatialSquare k : ℂ)) := by
  rw [actual_native_momentum_decomposition]
  simp only [Matrix.add_mulVec,Matrix.mulVec_add,Pi.add_apply,actual_native_static_temporal_reader]
  have ln := source_lapse_ne
  generalize hl : (lapse : ℂ)=L at ln ⊢
  field_simp [ln,Complex.ofReal_ne_zero.mpr nonzero]
  ring1

/-- The same actual corrected EM root retains the full quantum forcing in the solved Gauss read. -/
theorem actual_em_native_static_green_return (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (alpha beta : Fin 4) (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockClearing event eps n).eval 0≠0)
    (root : (0 : ℂ)∈visibleRoots (zeroClockFrequencyEMFraction event eps n alpha beta))
    (nonzero : spatialSquare ((eps^2 : ℝ) • n)≠0) :
    let r := emRestSlice (actualEMZeroClockMode event eps n beta 0)
    (nativeEMRestInsertion.transpose*ᵥr) 0=
      ((nativeEMRestInsertion.transpose*ᵥnativeQuantumSchurForcing (frequencyRay eps 0 n)
          (zeroClockQuantumResponse event eps 0 n) (actualEMZeroClockMode event eps n beta 0)) 0-
        (nativeEMRestInsertion.transpose*ᵥ(nativeSchurMatrix 0*ᵥr)) 0-
        (nativeEMRestInsertion.transpose*ᵥ(nativeMomentumLower (frequencyRay eps 0 n)*ᵥr)) 0)/
          (2*(lapse : ℂ)*(spatialSquare ((eps^2 : ℝ) • n) : ℂ)) := by
  dsimp only
  have paid := actual_em_quantum_auxiliary_schur event eps 0 n alpha beta balanced finite regular root
  rw [← actual_native_schur_matrix_action] at paid
  have ray : frequencyRay eps 0 n=physicalFrequencyMomentum 0 ((eps^2 : ℝ) • n) := by
    rw [← actual_physical_frequency_ray]
    simp only [sourceFrequency,mul_zero]
  rw [ray] at paid ⊢
  simp only [Complex.ofReal_zero] at paid
  rw [actual_native_static_temporal_solve _ nonzero,paid]

end LowEnergy.GaussComposite.ActualDressedEMNativeCoulomb
