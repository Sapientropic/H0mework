import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaGradedEuler
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRadiusResponseDecay
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceYukawaMixedCoframeBand
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceYukawaMixedVacuumBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialCross
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceYukawaCoefficientCommutator SourceClockYukawaTail SourceClockYukawaNormalizedCurrent
open SourceScalarPositiveBulkWard SourceRelativePowerTail SourceClockReflectedForm
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] state fullAction normalizedAction compressionCore defectAction

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (s : Bool) :
    Commute (multiply c hc) (fullAction s) := by
  unfold fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases s
  · exact (map_smul (sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm

private theorem radial_y_commute (v : Ambient) (s : Bool) :
    Commute (GaussRadialMomentum.commutatorAction v) (fullAction s) := by
  unfold GaussRadialMomentum.commutatorAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold fullAction
  cases s
  · exact (map_smul (sourceMap (scalarField z)) _ (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) _ (f z)).symm

private theorem bracket_product (A B C : End) :
    bracket (A*B) C=A*bracket B C+bracket A C*B := by unfold bracket;noncomm_ring

private theorem radial_term (s : Bool) (v : Ambient) :
    bracket (GaussRadialHamiltonian.radialTerm v) (fullAction s)=(-Complex.I) •
      (constantAction s v.1*multiply scalarWeight scalarWeight_smooth*GaussRadialMomentum.commutatorAction v+
        GaussRadialMomentum.commutatorAction v*multiply scalarWeight scalarWeight_smooth*constantAction s v.1) := by
  have hw : bracket (multiply scalarWeight scalarWeight_smooth) (fullAction s)=0 :=
    sub_eq_zero.mpr (real_full _ _ s).eq
  have hc : bracket (GaussRadialMomentum.commutatorAction v) (fullAction s)=0 :=
    sub_eq_zero.mpr (radial_y_commute v s).eq
  have hp : bracket (covariantMomentum v) (fullAction s)=(-Complex.I) • constantAction s v.1 := by
    apply LinearMap.ext
    intro f
    change covariantMomentum v (fullAction s f)-fullAction s (covariantMomentum v f)=_
    rw [SourceScalarGaugeForce.original_full_momentum,add_sub_cancel_left]
    rfl
  have ha := native_full_adjoint_commutator s v
  unfold GaussRadialHamiltonian.radialTerm
  change bracket (GaussMomentumAdjoint.adjoint v*(multiply scalarWeight scalarWeight_smooth*
    GaussRadialMomentum.commutatorAction v)+GaussRadialMomentum.commutatorAction v*
    (multiply scalarWeight scalarWeight_smooth*covariantMomentum v)) (fullAction s)=_
  have hadd (A B C : End) : bracket (A+B) C=bracket A C+bracket B C := by unfold bracket;noncomm_ring
  rw [hadd,bracket_product,bracket_product,bracket_product,bracket_product,hw,hc,hp,ha]
  simp only [mul_zero,zero_mul,zero_add,add_zero,mul_smul_comm,smul_mul_assoc,mul_assoc,smul_add]

private theorem scalar_radial_sum (sharp : Bool) :
    (∑ a : ScalarIndex,constantAction sharp (scalarBasis a)*
      SourceClosedCostNativeProbe.coordinateAction (scalarDirection a))=scalarAction sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.sum_apply,sum_apply]
  change (∑ a : ScalarIndex,branchMap sharp (scalarBasis a)
    ((inner ℝ (z.2.1 : Scalar) (scalarBasis a) : ℂ) • f z))=branchMap sharp (z.2.1 : Scalar) (f z)
  have he : ∑ a : ScalarIndex,(inner ℝ (z.2.1 : Scalar) (scalarBasis a)) • scalarBasis a=(z.2.1 : Scalar) := by
    simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm] using scalarBasis.sum_repr (z.2.1 : Scalar)
  conv_rhs => rw [←he,map_sum,sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul,map_smul]
  rfl

def crossCore (sharp : Bool) : End := (-(sourceTime 0:ℂ)/4) •
  (inverseVolumeAction*inverseAction^3*scalarAction sharp)

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private theorem radial_term_point (sharp : Bool) (a : ScalarIndex) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    ((-Complex.I) •
      (constantAction sharp (scalarDirection a).1*multiply scalarWeight scalarWeight_smooth*
          GaussRadialMomentum.commutatorAction (scalarDirection a)+
        GaussRadialMomentum.commutatorAction (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
          constantAction sharp (scalarDirection a).1)) f z=
      (-(sourceTime 0:ℂ)/2) • (((SourcePhysicalKineticSquare.reciprocalVolume z:ℂ)*(reciprocal z:ℂ)^3) •
        ((constantAction sharp (scalarBasis a)*SourceClosedCostNativeProbe.coordinateAction (scalarDirection a)) f z)) := by
  change (-Complex.I) •
    (branchMap sharp (scalarBasis a) ((scalarWeight z:ℂ) •
      (GaussRadialMomentum.commutatorFiber (scalarDirection a) z (f z)))+
      GaussRadialMomentum.commutatorFiber (scalarDirection a) z
        ((scalarWeight z:ℂ) • branchMap sharp (scalarBasis a) (f z)))=_
  unfold GaussRadialMomentum.commutatorFiber
  simp only [smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_smul]
  change (-Complex.I) •
    (((scalarWeight z:ℂ)*(-Complex.I*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ))) •
      branchMap sharp (scalarBasis a) (f z)+
      ((scalarWeight z:ℂ)*(-Complex.I*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ))) •
      branchMap sharp (scalarBasis a) (f z))=_
  rw [←add_smul,smul_smul]
  change _=((-(sourceTime 0:ℂ)/2)*((SourcePhysicalKineticSquare.reciprocalVolume z:ℂ)*(reciprocal z:ℂ)^3)) •
    branchMap sharp (scalarBasis a) ((inner ℝ (z.2.1:Scalar) (scalarBasis a):ℂ) • f z)
  rw [map_smul,smul_smul]
  congr 1
  unfold GaussRadialMomentum.radialDerivative
  change (-Complex.I)*((scalarWeight z:ℂ)*(-Complex.I*((-inner ℝ (z.2.1:Scalar) (scalarBasis a)/(4*radius z^3):ℝ):ℂ))+
    (scalarWeight z:ℂ)*(-Complex.I*((-inner ℝ (z.2.1:Scalar) (scalarBasis a)/(4*radius z^3):ℝ):ℂ)))=_
  have hw : scalarWeight z= -sourceTime 0*SourcePhysicalKineticSquare.reciprocalVolume z := by
    unfold scalarWeight SourcePhysicalKineticSquare.reciprocalVolume
    ring
  rw [hw]
  unfold reciprocal
  push_cast
  simp only [div_eq_mul_inv,inv_pow,mul_inv_rev]
  linear_combination (norm := ring) (sourceTime 0:ℂ)*(SourcePhysicalKineticSquare.reciprocalVolume z:ℂ)*
    (inner ℝ (z.2.1:Scalar) (scalarBasis a):ℂ)*((radius z:ℂ)⁻¹)^3/2*Complex.I_mul_I

/-- The complete cross-Y radial current loses every differential exterior leg. -/
theorem original_radial_yukawa_cross (sharp : Bool) :
    bracket GaussRadialHamiltonian.radialAction (fullAction sharp)=crossCore sharp := by
  have hsum : bracket GaussRadialHamiltonian.radialAction (fullAction sharp)=
      (1/2:ℂ) • ∑ a : ScalarIndex,bracket (GaussRadialHamiltonian.radialTerm (scalarDirection a)) (fullAction sharp) := by
    simp only [GaussRadialHamiltonian.radialAction,bracket,smul_mul_assoc,mul_smul_comm,←smul_sub,
      Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
  rw [hsum]
  simp_rw [radial_term]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let ev : QuantumTest →ₗ[ℂ] FockFiber :=
    { toFun := fun q => q z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev (((1/2:ℂ) • ∑ a : ScalarIndex,(-Complex.I) •
      (constantAction sharp (scalarDirection a).1*multiply scalarWeight scalarWeight_smooth*GaussRadialMomentum.commutatorAction (scalarDirection a)+
        GaussRadialMomentum.commutatorAction (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*constantAction sharp (scalarDirection a).1)) f)=_
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum]
  change (1/2:ℂ) • (∑ a : ScalarIndex,((-Complex.I) •
      (constantAction sharp (scalarDirection a).1*multiply scalarWeight scalarWeight_smooth*GaussRadialMomentum.commutatorAction (scalarDirection a)+
        GaussRadialMomentum.commutatorAction (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*constantAction sharp (scalarDirection a).1)) f z)=_
  simp_rw [radial_term_point]
  rw [←Finset.smul_sum,←Finset.smul_sum]
  have hs := congrArg (fun A : End => A f z) (scalar_radial_sum sharp)
  simp only [LinearMap.sum_apply,sum_apply] at hs
  rw [hs]
  change (1/2:ℂ) • ((-(sourceTime 0:ℂ)/2) •
    (((SourcePhysicalKineticSquare.reciprocalVolume z:ℂ)*(reciprocal z:ℂ)^3) • scalarAction sharp f z))=_
  unfold crossCore
  change _=(-(sourceTime 0:ℂ)/4) • (inverseVolumeAction ((inverseAction^3) (scalarAction sharp f))) z
  rw [inverseVolumeAction,multiply_apply,inverse_power_apply]
  simp only [smul_smul]
  congr 1
  ring

/-- The actual source return retains the whole mixed compression defect. -/
theorem actual_corrected_radial_yukawa_cross (sharp : Bool) (F : Index) :
    bracket (SourceRadiusResponseDecay.radialCurrent F) (fullAction sharp)=crossCore sharp-
      bracket (bracket (defectAction F) inverseAction) (fullAction sharp) := by
  have h := original_radial_yukawa_cross sharp
  unfold SourceRadiusResponseDecay.radialCurrent bracket at *
  linear_combination (norm := noncomm_ring) h

/-- All radial growth in the cross source is paid by the original bounded B map. -/
theorem original_cross_normalized_return (sharp : Bool) :
    crossCore sharp=(-(sourceTime 0:ℂ)/4) • (inverseVolumeAction*inverseAction^2*
      (normalizedAction sharp-inverseAction*constantAction sharp vacuum)) := by
  have h : fullAction sharp=scalarAction sharp+constantAction sharp vacuum := by rw [full_scalar_split,add_comm]
  rw [crossCore,normalizedAction,h]
  congr 1
  noncomm_ring

end LowEnergy.SourceClockYukawaRadialCross
