import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalField
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationNonlinearSourceTube

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTemporalCharge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential
open GaussQuantumMultiplier GaussNativeMatter
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceFieldFamily PreparationVacuumLowerClassical PreparationVacuumNonlinearFieldCurve
open CanonicalGradedSpatialSource CanonicalGradedCurrent CanonicalGradedCharge
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff BigOperators Topology
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

def temporalCoefficient (a : Fin 12) (i : Fin 4) : SourceMatrix :=
  if i=0 then Complex.I • nativePrimal (originalUnit a) else 0

theorem temporal_affine (a : Fin 12) (p : PhysicalMomentum) :
    affineMatrix (temporalCoefficient a) p=Complex.I • nativePrimal (originalUnit a) := by
  simp [affineMatrix,temporalCoefficient]

theorem temporal_full_matrix (a : Fin 12) (p : PhysicalMomentum) :
    realFourierMatrix (temporalCoefficient a) p=chargeMatrix (originalUnit a) := by
  rw [realFourierMatrix,temporal_affine,temporal_affine]
  ext u v
  cases u <;> cases v <;>
    simp [chargeMatrix,nativeFull,Matrix.fromBlocks,Matrix.smul_apply,Matrix.map_apply]

theorem temporal_full_family (a : Fin 12) (p : PhysicalMomentum) (z : physicalChart) :
    fullFamily (temporalField a) p z.val=chargeMatrix (originalUnit a) := by
  have coefficients : familyReader (temporalField a) z.val=temporalCoefficient a :=
    funext (temporal_family_reader a z)
  rw [fullFamily,coefficients,temporal_full_matrix]

theorem temporal_state_fiber (a : Fin 12) (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) : stateFiber (temporalField a) p s=quantized (chargeMatrix (originalUnit a)) := by
  have coefficients : (fun i=>statePhase s*densityVariation (temporalField a) s i)=temporalCoefficient a :=
    funext (temporal_normalized_reader a s valid.1 valid.2)
  unfold stateFiber
  rw [coefficients]
  exact congrArg quantizer (temporal_full_matrix a p)

theorem temporal_core (a : Fin 12) (p : PhysicalMomentum) (test : QuantumTest) :
    familyCore (temporalField a) p test=chargeAction (originalUnit a) test := by
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · change quantized (fullFamily (temporalField a) p z) (test z)=_
    rw [temporal_full_family a p ⟨z,inside⟩]
    rfl
  · have zero : test z=0 := image_eq_zero_of_notMem_tsupport (fun h=>inside (test.tsupport_subset h))
    change quantized (fullFamily (temporalField a) p z) (test z)=quantized (chargeMatrix (originalUnit a)) (test z)
    rw [zero,map_zero,map_zero]

abbrev globalReader (a : Fin 12) : H →L[ℂ] H := chargeReader (originalUnit a)

theorem globalReader_source (a : Fin 12) (p : PhysicalMomentum) (test : QuantumTest) :
    globalReader a (embed test)=embed (familyCore (temporalField a) p test) := by
  rw [temporal_core]
  exact chargeReader_core (originalUnit a) test

def chargePrice (a : Fin 12) : ℝ := ‖quantized (chargeMatrix (originalUnit a))‖

theorem chargePrice_nonnegative (a : Fin 12) : 0 ≤ chargePrice a := norm_nonneg _

theorem globalReader_norm (a : Fin 12) : ‖globalReader a‖ ≤ chargePrice a :=
  GaussBoundedMultiplier.extension_norm (fun _=>quantized (chargeMatrix (originalUnit a)))
    (fun _=>contDiffAt_const) (fun _ w=>weight_commute w (chargeMatrix (originalUnit a)))
    _ (norm_nonneg _) (fun _ f=>(quantized (chargeMatrix (originalUnit a))).le_opNorm f)

theorem temporal_hamiltonian (a : Fin 12) (s : ActionState) (valid : s∈validStates)
    (r : ℝ) (i : Fin 4) :
    stateHamiltonian (temporalCurve a s r) i=stateHamiltonian s i-r • temporalCoefficient a i := by
  have unit:=principalMatrix_regular s.1 valid.2
  unfold stateHamiltonian
  rw [temporalCurve_coframe,temporal_lower]
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Fin.cases_zero,temporalCoefficient,if_true,timeSymbol,mul_add,mul_smul_comm,
      ←mul_assoc,Ring.inverse_mul_cancel _ unit,one_mul,smul_add]
    rw [smul_comm (-Complex.I) r]
    simp only [neg_smul,smul_neg,sub_eq_add_neg]
  · simp [temporalCoefficient]

theorem temporal_hamiltonian_valid (a : Fin 12) (s : ActionState) (valid : s∈validStates) (r : ℝ) :
    temporalCurve a s r∈validStates := by
  change (temporalCurve a s r).1.det≠0 ∧
    StageNineCurrentCoframeMatterTemporalPrincipal.coframeTemporalPrincipalScalar (temporalCurve a s r).1≠0
  rw [temporalCurve_coframe]
  exact valid

theorem temporal_hamiltonian_first (a : Fin 12) (z : physicalChart) (i : Fin 4) (r : ℝ) :
    HasDerivAt (fun t=>stateHamiltonian (temporalCurve a (sourceState z.val) t) i)
      (-temporalCoefficient a i) r := by
  have actual:=(hasDerivAt_const r (stateHamiltonian (sourceState z.val) i)).sub
    ((hasDerivAt_id r).smul_const (temporalCoefficient a i))
  convert! actual using 1 <;> simp only [temporal_hamiltonian a _ (sourceState_valid z),one_smul,zero_sub,id_eq]; rfl

theorem temporal_contact_balance (a : Fin 12) (g : Field289) (z : physicalChart) (i : Fin 4) :
    phaseVariation g (sourceState z.val)*familyDensity (temporalField a) z.val i+
      familyPhase z.val*(densitySecond (temporalField a) g (sourceState z.val) i+
        shellSecond (temporalField a) g (sourceState z.val) i)=0 := by
  have path : ContinuousAt (fun r : ℝ=>sourceState z.val+r • fieldDirection g) 0 := by fun_prop
  have base : sourceState z.val+(0:ℝ) • fieldDirection g∈validStates := by
    simpa only [zero_smul,add_zero] using sourceState_valid z
  have remains:=path.eventually (validStates_open.mem_nhds base)
  have same : (fun r : ℝ=>statePhase (sourceState z.val+r • fieldDirection g)*
      densityVariation (temporalField a) (sourceState z.val+r • fieldDirection g) i)=ᶠ[𝓝 0]
        fun _=>temporalCoefficient a i := by
    filter_upwards [remains] with r hr
    exact temporal_normalized_reader a _ hr.1 hr.2 i
  have zero : HasDerivAt (fun r : ℝ=>statePhase (sourceState z.val+r • fieldDirection g)*
      densityVariation (temporalField a) (sourceState z.val+r • fieldDirection g) i) 0 0 :=
    (hasDerivAt_const 0 (temporalCoefficient a i)).congr_of_eventuallyEq same
  exact (actual_normalized_family_derivative (temporalField a) g z i).unique zero

theorem temporal_contact_fiber (a : Fin 12) (g : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    contactFiber (temporalField a) g p z.val=0 := by
  have same : stateFiber (temporalField a) p=ᶠ[𝓝 (sourceState z.val)]
      fun _=>quantized (chargeMatrix (originalUnit a)) := by
    filter_upwards [validStates_open.mem_nhds (sourceState_valid z)] with s hs
    exact temporal_state_fiber a p s hs
  unfold contactFiber
  rw [same.fderiv_eq,fderiv_const_apply]
  rfl

theorem temporal_contact_core (a : Fin 12) (g : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    familyContactCore (temporalField a) g p test=0 := by
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · change contactFiber (temporalField a) g p z (test z)=0
    rw [temporal_contact_fiber a g p ⟨z,inside⟩]
    rfl
  · have zero : test z=0 := image_eq_zero_of_notMem_tsupport (fun h=>inside (test.tsupport_subset h))
    change contactFiber (temporalField a) g p z (test z)=0
    rw [zero,map_zero]

end LowEnergy.PreparationVacuumTemporalCharge
