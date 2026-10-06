import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaCurrentForm
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceYukawaCoefficientCommutator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaCubicCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussDiagonalHistory
open GaussUnitaryHistory GaussHistoryHilbert SourceQuantumConfigurationHilbert
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceScalarPairedTransport
open SourceClockYukawaCurrent SourceClockYukawaHamiltonianCurrent SourceYukawaCoefficientCommutator
open FullYSourceResolventGraphSplice SourceRelativePowerTail
open SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent GaussNativeEnergy GaussNativePotential
open GaussLiveMomentum SourceQuantumFockGauge SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction state fullAction

def sourceDerivative (sharp : Bool) (A : End) : End := bracket A (fullAction sharp)

private theorem derivative_add (s : Bool) (A B : End) :
    sourceDerivative s (A+B)=sourceDerivative s A+sourceDerivative s B := by
  unfold sourceDerivative bracket
  noncomm_ring

private theorem derivative_sub (s : Bool) (A B : End) :
    sourceDerivative s (A-B)=sourceDerivative s A-sourceDerivative s B := by
  unfold sourceDerivative bracket
  noncomm_ring

private theorem derivative_neg (s : Bool) (A : End) :
    sourceDerivative s (-A)= -sourceDerivative s A := by
  unfold sourceDerivative bracket
  noncomm_ring

private theorem derivative_mul (s : Bool) (A B : End) :
    sourceDerivative s (A*B)=sourceDerivative s A*B+A*sourceDerivative s B := by
  unfold sourceDerivative bracket
  noncomm_ring

private theorem derivative_smul (s : Bool) (c : ℂ) (A : End) :
    sourceDerivative s (c • A)=c • sourceDerivative s A := by
  simp only [sourceDerivative,bracket,smul_mul_assoc,mul_smul_comm,smul_sub]

private theorem derivative_sum {ι : Type*} (s : Bool) (I : Finset ι) (A : ι → End) :
    sourceDerivative s (∑ i ∈ I,A i)=∑ i ∈ I,sourceDerivative s (A i) := by
  simp only [sourceDerivative,bracket,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]

private theorem derivative_self (s : Bool) : sourceDerivative s (fullAction s)=0 := by
  simp only [sourceDerivative,bracket,sub_self]

private theorem derivative_of_commute (s : Bool) (A : End) (h : Commute A (fullAction s)) :
    sourceDerivative s A=0 := sub_eq_zero.mpr h.eq

private theorem derivative_real (s : Bool) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    sourceDerivative s (multiply c hc)=0 := by
  apply derivative_of_commute
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases s
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm

private theorem derivative_native (s : Bool) (v : Ambient) :
    sourceDerivative s (covariantMomentum v)=(-Complex.I) • constantAction s v.1 := by
  apply LinearMap.ext
  intro f
  change covariantMomentum v (fullAction s f)-fullAction s (covariantMomentum v f)=_
  rw [SourceScalarGaugeForce.original_full_momentum]
  abel

def sourceCurvature (sharp : Bool) : End :=
  -(∑ a : ScalarIndex,constantAction sharp (scalarDirection a).1*
    multiply scalarWeight scalarWeight_smooth*constantAction sharp (scalarDirection a).1)+
    (3/2 : ℂ) • (spinVolume*(spinVariation sharp 3*spinVariation sharp 3-
      spinVariation sharp 0*spinVariation sharp 0-spinVariation sharp 1*spinVariation sharp 1-
        spinVariation sharp 2*spinVariation sharp 2))

private theorem scalar_curvature_algebra (s : Bool)
    (hM : ∀ a : ScalarIndex,sourceDerivative s (constantAction s (scalarDirection a).1)=0)
    (hA : ∀ a : ScalarIndex,sourceDerivative s (GaussMomentumAdjoint.adjoint (scalarDirection a))=
      (-Complex.I) • constantAction s (scalarDirection a).1) :
    sourceDerivative s (scalarCurrent s)=
      -(∑ a : ScalarIndex,constantAction s (scalarDirection a).1*
        multiply scalarWeight scalarWeight_smooth*constantAction s (scalarDirection a).1) := by
  unfold scalarCurrent
  rw [derivative_smul,derivative_sum]
  simp only [derivative_add,derivative_mul,derivative_native,derivative_real,hM,hA,
    zero_mul,mul_zero,add_zero,zero_add,smul_mul_assoc,mul_smul_comm]
  simp only [←add_smul]
  rw [←Finset.smul_sum,smul_smul]
  have hc : (-Complex.I/2 : ℂ)*((-Complex.I)+(-Complex.I))= -1 := by
    calc
      _=Complex.I*Complex.I := by ring
      _= -1 := Complex.I_mul_I
  rw [hc,neg_one_smul]

private theorem spin_curvature_algebra (s : Bool)
    (hK : ∀ j : Fin 4,sourceDerivative s (spinVariation s j)=0) :
    sourceDerivative s (reducedSpinCurrent s)=
      (3/2 : ℂ) • (spinVolume*(spinVariation s 3*spinVariation s 3-
        spinVariation s 0*spinVariation s 0-spinVariation s 1*spinVariation s 1-
          spinVariation s 2*spinVariation s 2)) := by
  have hV : sourceDerivative s spinVolume=0 := derivative_real s _ _
  have hJ (j : Fin 4) : sourceDerivative s (activeSpin j)=spinVariation s j := rfl
  simp only [reducedSpinCurrent,derivative_smul,derivative_mul,derivative_sub,hV,hK,hJ,
    derivative_self,zero_mul,zero_add,sub_zero]

private theorem curvature_derivative_zero (s : Bool)
    (hM : ∀ a : ScalarIndex,sourceDerivative s (constantAction s (scalarDirection a).1)=0)
    (hK : ∀ j : Fin 4,sourceDerivative s (spinVariation s j)=0) :
    sourceDerivative s (sourceCurvature s)=0 := by
  have hV : sourceDerivative s spinVolume=0 := derivative_real s _ _
  simp only [sourceCurvature,derivative_add,derivative_neg,derivative_sum,derivative_smul,
    derivative_mul,derivative_sub,derivative_real,hM,hK,hV,zero_mul,mul_zero,add_zero,
    sub_self,Finset.sum_const_zero,neg_zero,smul_zero]

private theorem constant_derivative_zero (s : Bool) (a : ScalarIndex) :
    sourceDerivative s (constantAction s (scalarDirection a).1)=0 :=
  derivative_of_commute s _ (fullY_constant_commute s _).symm

private theorem spin_derivative_zero (s : Bool) (j : Fin 4) :
    sourceDerivative s (spinVariation s j)=0 :=
  derivative_of_commute s _ (fullY_spinVariation_commute s j).symm

/-- The second source current is the literal seventy-scalar and four-spin quadratic word. -/
theorem original_hamiltonian_second_source (sharp : Bool) :
    sourceDerivative sharp (sourceDerivative sharp diagonalAction)=sourceCurvature sharp := by
  have h : sourceDerivative sharp diagonalAction=originalCurrent sharp :=
    original_hamiltonian_yukawa_current sharp
  rw [h]
  unfold originalCurrent
  rw [derivative_add,derivative_add]
  have hm : sourceDerivative sharp (bracket GaussMatterCore.matterAction (fullAction sharp))=0 :=
    matter_current_Y_zero sharp
  rw [hm,zero_add,scalar_curvature_algebra sharp (constant_derivative_zero sharp)
    (fun a => native_full_adjoint_commutator sharp (scalarDirection a)),
    spin_curvature_algebra sharp (spin_derivative_zero sharp)]
  rfl

private theorem derivative_two (s : Bool) : sourceDerivative s (2:End)=0 := by
  unfold sourceDerivative bracket
  noncomm_ring

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

def resolventCore (F : Index) (z : ℂ) (hz : z.im≠0) : End where
  toFun f := state F z hz (coreEquiv f)
  map_add' f g := by
    apply embed_injective
    simp only [state_embed,map_add,Submodule.coe_add]
  map_smul' c f := by
    apply embed_injective
    simp only [state_embed,map_smul,RingHom.id_apply,Submodule.coe_smul]

private theorem resolvent_core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := state_embed F z hz (coreEquiv f)

/-- The actual source Y derivative of the same-F resolvent is its full corrected
current sandwich, on the original core and without a graph hypothesis. -/
theorem actual_resolvent_first_source (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) :
    sourceDerivative sharp (resolventCore F z hz)=
      -(resolventCore F z hz*SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F*
        resolventCore F z hz) := by
  apply LinearMap.ext
  intro f
  apply embed_injective
  have h := actual_yukawa_resolvent_transport sharp F z hz (coreEquiv f)
  simp only [yukawaSource,currentResponse,coreEquiv.symm_apply_apply] at h
  change embed (fullAction sharp (resolventCore F z hz f))=
    finiteResolvent F z (embed (fullAction sharp f))+
    finiteResolvent F z (embed (SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F
      (resolventCore F z hz f))) at h
  simp only [sourceDerivative,bracket,LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply,
    map_sub,map_neg,resolvent_core_embed]
  linear_combination (norm := module) -h

private theorem resolvent_second_algebra (s : Bool) (R D : End)
    (h : sourceDerivative s R= -(R*D*R)) :
    sourceDerivative s (sourceDerivative s R)=
      2*(R*D*R*D*R)-R*sourceDerivative s D*R := by
  rw [h]
  simp only [derivative_neg,derivative_mul,h]
  noncomm_ring

private theorem resolvent_third_algebra (s : Bool) (R D : End)
    (h : sourceDerivative s R= -(R*D*R)) :
    sourceDerivative s (sourceDerivative s (sourceDerivative s R))=
      -6*(R*D*R*D*R*D*R)+3*(R*sourceDerivative s D*R*D*R)+
      3*(R*D*R*sourceDerivative s D*R)-R*sourceDerivative s (sourceDerivative s D)*R := by
  rw [resolvent_second_algebra s R D h]
  simp only [derivative_sub,derivative_mul,derivative_two,h,zero_mul,zero_add]
  noncomm_ring

def correctedCurvature (sharp : Bool) (F : Index) : End :=
  sourceDerivative sharp (SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F)

def sourceThird (sharp : Bool) : End :=
  sourceDerivative sharp (sourceDerivative sharp (sourceDerivative sharp diagonalAction))

def defectThird (sharp : Bool) (F : Index) : End :=
  sourceDerivative sharp (sourceDerivative sharp (sourceDerivative sharp (defectAction F)))

/-- The actual Hamiltonian closes at third right Yukawa derivative on the full CAR core. -/
theorem original_hamiltonian_third_source (sharp : Bool) : sourceThird sharp=0 := by
  rw [sourceThird,original_hamiltonian_second_source]
  exact curvature_derivative_zero sharp (constant_derivative_zero sharp) (spin_derivative_zero sharp)

/-- Compression retains its complete second defect after the original source curvature is generated. -/
theorem actual_corrected_curvature (sharp : Bool) (F : Index) :
    correctedCurvature sharp F=sourceCurvature sharp-
      sourceDerivative sharp (sourceDerivative sharp (defectAction F)) := by
  have h : SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F=
      sourceDerivative sharp diagonalAction-sourceDerivative sharp (defectAction F) := by
    unfold SourceClockYukawaHamiltonianCurrent.correctedCurrent sourceDerivative
    rw [original_hamiltonian_yukawa_current]
  rw [correctedCurvature,h,derivative_sub,original_hamiltonian_second_source]

private theorem corrected_third (sharp : Bool) (F : Index) :
    sourceDerivative sharp (sourceDerivative sharp (SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F))=
      sourceThird sharp-defectThird sharp F := by
  have h : SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F=
      sourceDerivative sharp diagonalAction-sourceDerivative sharp (defectAction F) := by
    unfold SourceClockYukawaHamiltonianCurrent.correctedCurrent sourceDerivative
    rw [original_hamiltonian_yukawa_current]
  rw [h,derivative_sub,derivative_sub]
  rfl

/-- Every third source derivative left in the actual compression is its signed full defect. -/
theorem actual_compression_third_source (sharp : Bool) (F : Index) :
    sourceDerivative sharp (sourceDerivative sharp (sourceDerivative sharp (compressionCore F)))=
      -defectThird sharp F := by
  have h : sourceDerivative sharp (compressionCore F)=
      SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F := original_compression_yukawa_current sharp F
  rw [h,corrected_third,original_hamiltonian_third_source,zero_sub]

/-- Exact cubic source-resolvent response consumes the original quadratic closure
while preserving the complete same-F compression third defect. -/
theorem actual_resolvent_third_source (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) :
    let R := resolventCore F z hz
    let D := SourceClockYukawaHamiltonianCurrent.correctedCurrent sharp F
    let E := correctedCurvature sharp F
    sourceDerivative sharp (sourceDerivative sharp (sourceDerivative sharp R))=
      -6*(R*D*R*D*R*D*R)+3*(R*E*R*D*R)+3*(R*D*R*E*R)+
        R*defectThird sharp F*R := by
  dsimp only
  rw [resolvent_third_algebra sharp _ _ (actual_resolvent_first_source sharp F z hz),
    corrected_third,original_hamiltonian_third_source,zero_sub]
  simp only [correctedCurvature,mul_neg,neg_mul,sub_neg_eq_add]

end LowEnergy.SourceClockYukawaCubicCurrent
