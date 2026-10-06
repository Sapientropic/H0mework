import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaHamiltonianCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceYukawaCoefficientCommutator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceYukawaMixedCurvature
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open GaussMatterCore GaussLiveMomentum SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarGaugeForce SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent
open SourceScalarPairedTransport FullYSourceResolventGraphSplice
open SourceClockYukawaHamiltonianCurrent SourceYukawaCoefficientCommutator
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction

/-- This opposite-branch coefficient commutator is retained in the native first-order word. -/
def mixedCoefficient (sharp : Bool) (a : ScalarIndex) : End :=
  bracket (constantAction sharp (scalarDirection a).1) (fullAction (!sharp))

/-- All seventy native scalar directions retain both the first-order word and CAR anticommutator. -/
def scalarMixed (sharp : Bool) : End :=
  (-Complex.I/2 : ℂ) • ∑ a : ScalarIndex,
    (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
        mixedCoefficient sharp a+
      mixedCoefficient sharp a*multiply scalarWeight scalarWeight_smooth*
        covariantMomentum (scalarDirection a))-
  (1/2 : ℂ) • ∑ a : ScalarIndex,
    (constantAction (!sharp) (scalarDirection a).1*multiply scalarWeight scalarWeight_smooth*
        constantAction sharp (scalarDirection a).1+
      constantAction sharp (scalarDirection a).1*multiply scalarWeight scalarWeight_smooth*
        constantAction (!sharp) (scalarDirection a).1)

def spinMixedRow (sharp : Bool) (j : Fin 4) : End :=
  spinVariation sharp j*spinVariation (!sharp) j+
    bracket (spinVariation sharp j) (fullAction (!sharp))*activeSpin j

/-- The actual boost/chiral signs and the full opposite-branch Yukawa commutator remain. -/
def spinMixed (sharp : Bool) : End := (3/2 : ℂ) • (spinVolume*
  (spinMixedRow sharp 3-spinMixedRow sharp 0-spinMixedRow sharp 1-spinMixedRow sharp 2-
    bracket (fullAction sharp) (fullAction (!sharp))))

def matterMixed (sharp : Bool) : End := ∑ i : Fin 3,∑ b : Fin 3,
  bracket (bracket (GaussQuantumMultiplier.action (localMatrix i b) (local_smooth i b))
    (fullAction sharp)) (fullAction (!sharp))

/-- One complex source word; neither mixed CAR terms nor compression effects are discarded. -/
def mixedCurvature (sharp : Bool) : End := matterMixed sharp+scalarMixed sharp+spinMixed sharp

def correctedMixedCurvature (sharp : Bool) (F : Index) : End :=
  mixedCurvature sharp-
    bracket (bracket (defectAction F) (fullAction sharp)) (fullAction (!sharp))

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (fullAction sharp) := by
  unfold fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm

private theorem native_full_current (sharp : Bool) (v : Ambient) :
    bracket (covariantMomentum v) (fullAction sharp)=(-Complex.I) • constantAction sharp v.1 := by
  apply LinearMap.ext
  intro f
  change covariantMomentum v (fullAction sharp f)-fullAction sharp (covariantMomentum v f)=_
  rw [SourceScalarGaugeForce.original_full_momentum]
  abel

private theorem bracket_add {R : Type*} [Ring R] (A B C : R) :
    bracket (A+B) C=bracket A C+bracket B C := by unfold bracket;noncomm_ring

private theorem bracket_sub {R : Type*} [Ring R] (A B C : R) :
    bracket (A-B) C=bracket A C-bracket B C := by unfold bracket;noncomm_ring

private theorem bracket_product {R : Type*} [Ring R] (A B C : R) :
    bracket (A*B) C=A*bracket B C+bracket A C*B := by unfold bracket;noncomm_ring

private theorem bracket_smul {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (c : ℂ) (A B : R) :
    bracket (c • A) B=c • bracket A B := by
  simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]

private theorem bracket_sum {R ι : Type*} [Ring R] [Fintype ι] (A : ι → R) (B : R) :
    bracket (∑ i,A i) B=∑ i,bracket (A i) B := by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]

private theorem bracket_commute {R : Type*} [Ring R] {A B : R} (h : Commute A B) : bracket A B=0 :=
  sub_eq_zero.mpr h.eq

private theorem scalar_term_mixed {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (P A W M Y C : R)
    (hP : bracket P Y=(-Complex.I) • C) (hA : bracket A Y=(-Complex.I) • C)
    (hW : Commute W Y) :
    bracket (A*W*M+M*W*P) Y=
      A*W*bracket M Y+bracket M Y*W*P+(-Complex.I) • (C*W*M+M*W*C) := by
  simp only [bracket_add,bracket_product,hP,hA,bracket_commute hW,zero_mul,
    add_zero,smul_mul_assoc,mul_smul_comm,mul_assoc,smul_add]
  module

private theorem scalar_constant : (-Complex.I/2 : ℂ)*(-Complex.I)= -(1/2 : ℂ) := by
  calc
    _ = (Complex.I*Complex.I)/2 := by ring
    _ = _ := by rw [Complex.I_mul_I];ring

/-- The mixed scalar current exposes its actual native first derivatives and full CAR products. -/
theorem original_mixed_scalar_source (sharp : Bool) :
    bracket (scalarCurrent sharp) (fullAction (!sharp))=scalarMixed sharp := by
  have h (a : ScalarIndex) := scalar_term_mixed
    (covariantMomentum (scalarDirection a)) (GaussMomentumAdjoint.adjoint (scalarDirection a))
    (multiply scalarWeight scalarWeight_smooth) (constantAction sharp (scalarDirection a).1)
    (fullAction (!sharp)) (constantAction (!sharp) (scalarDirection a).1)
    (native_full_current (!sharp) _) (native_full_adjoint_commutator (!sharp) _)
    (real_full _ _ (!sharp))
  unfold scalarCurrent scalarMixed mixedCoefficient
  rw [bracket_smul,bracket_sum]
  simp_rw [h]
  rw [Finset.sum_add_distrib,←Finset.smul_sum,smul_add,smul_smul,scalar_constant]
  simp only [sub_eq_add_neg,neg_smul]

private theorem spin_mixed_return (sharp : Bool) :
    bracket (reducedSpinCurrent sharp) (fullAction (!sharp))=spinMixed sharp := by
  have hV : Commute spinVolume (fullAction (!sharp)) :=
    real_full GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth (!sharp)
  unfold reducedSpinCurrent spinMixed spinMixedRow
  rw [bracket_smul,bracket_product,bracket_commute hV]
  simp only [zero_mul,add_zero,bracket_sub,bracket_product]
  rfl

private theorem matter_mixed_return (sharp : Bool) :
    bracket (bracket matterAction (fullAction sharp)) (fullAction (!sharp))=matterMixed sharp := by
  simp only [matterAction,matterMixed,bracket_sum]

/-- The original full Hamiltonian current generates the complete opposite-branch mixed source. -/
theorem original_mixed_hamiltonian_source (sharp : Bool) :
    bracket (originalCurrent sharp) (fullAction (!sharp))=mixedCurvature sharp := by
  simp only [originalCurrent,mixedCurvature,bracket_add,original_mixed_scalar_source,
    spin_mixed_return,matter_mixed_return]

/-- The same-F mixed response keeps the entire actual compression double commutator. -/
theorem actual_mixed_compression_source (sharp : Bool) (F : Index) :
    bracket (correctedCurrent sharp F) (fullAction (!sharp))=correctedMixedCurvature sharp F := by
  rw [correctedCurrent,correctedMixedCurvature,bracket_sub,original_mixed_hamiltonian_source]

end LowEnergy.SourceYukawaMixedCurvature
