import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussRadialMomentumDomain
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussFullHamiltonian

/-! The full original Hamiltonian consumes the actual radial momentum commutators. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussRadialHamiltonian
open GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum GaussMomentumAdjoint GaussYukawaCoefficient
open GaussRadialDomain GaussRadialMomentum GaussRadialMomentumDomain GaussFockPair GaussNativeForm GaussNativePotential
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

theorem multiplier_commutes (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) :
    Commute (localMultiplier A smooth) inverseAction := by
  change (localMultiplier A smooth)*inverseAction=inverseAction*(localMultiplier A smooth)
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (reciprocal z : ℂ) (f z)

theorem real_commutes (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c smooth) inverseAction := multiplier_commutes _ _

private theorem test_pair_ext (f g : QuantumTest)
    (h : ∀ a, sourcePair a f=sourcePair a g) : f=g := by
  have hz : inner ℂ (embed (f-g)) (embed (f-g)) = 0 := by
    calc
      _ = sourcePair (f-g) f-sourcePair (f-g) g := by
        conv_lhs => rw [show embed (f-g)=embed f-embed g from map_sub embed f g]
        exact inner_sub_right _ _ _
      _ = 0 := sub_eq_zero.mpr (h (f-g))
  apply sub_eq_zero.mp
  exact embed_injective (((inner_self_eq_zero (𝕜 := ℂ)).mp hz).trans (map_zero embed).symm)

theorem paired_commutes (A B : End) (pair : GaussCoframeForm.Paired B A)
    (commutes : Commute A inverseAction) : Commute B inverseAction := by
  change B*inverseAction=inverseAction*B
  apply LinearMap.ext
  intro g
  apply test_pair_ext
  intro f
  have hc : A (inverseAction f)=inverseAction (A f) := LinearMap.congr_fun commutes.eq f
  change sourcePair f (B (inverseAction g))=sourcePair f (inverseAction (B g))
  calc
    _ = sourcePair (A f) (inverseAction g) := pair f (inverseAction g)
    _ = sourcePair (inverseAction (A f)) g := multiply_pair reciprocal _ (A f) g
    _ = sourcePair (A (inverseAction f)) g := by rw [hc]
    _ = sourcePair (inverseAction f) (B g) := (pair (inverseAction f) g).symm
    _ = _ := (multiply_pair reciprocal _ f (B g)).symm

theorem coframe_derivative (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) inverseAction := by
  change _*inverseAction=inverseAction*_
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeCore.derivative _ (inverseAction f) z = inverseAction (GaussCoframeCore.derivative _ f) z
  rw [GaussCoframeCore.derivative_apply,inverseAction_real,
    fderiv_fun_smul (reciprocal_smooth.differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  have hd : fderiv ℝ reciprocal z (GaussCoframeCore.coframeDirection i)=0 := by
    rw [reciprocal_derivative]
    change -inner ℝ (z.2.1 : SourceQuantumScalarChart.Scalar) 0 / _ = 0
    simp
  change reciprocal z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
    fderiv ℝ reciprocal z (GaussCoframeCore.coframeDirection i) • f z = _
  rw [hd,zero_smul,add_zero]
  change _ = (reciprocal z : ℂ) • GaussCoframeCore.derivative _ f z
  rw [GaussCoframeCore.derivative_apply]
  apply PiLp.ext
  intro word
  exact Complex.real_smul

theorem coframe_momentum (i : Fin 6) : Commute (GaussCoframeCore.momentum i) inverseAction :=
  (coframe_derivative i).smul_left (-Complex.I)

theorem coframe_adjoint (i : Fin 6) : Commute (GaussCoframeCore.adjoint i) inverseAction :=
  paired_commutes _ _ (GaussCoframeKinetic.adjoint_pair i) (coframe_momentum i)

theorem quantum_commutes (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val) :
    Commute (GaussQuantumMultiplier.action A smooth) inverseAction := multiplier_commutes _ _

theorem coframe_kinetic : Commute GaussCoframeKinetic.kinetic inverseAction := by
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  exact (coframe_adjoint i).mul_left ((real_commutes _ _).mul_left (coframe_momentum j))

theorem coframe_current (a : Fin 7) : Commute (GaussCoframeSpin.current a) inverseAction :=
  quantum_commutes _ _

theorem coframe_mixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeForm.mixed i a c smooth) inverseAction :=
  (((coframe_current a).mul_left ((real_commutes c smooth).mul_left (coframe_momentum i))).add_left
    ((coframe_adjoint i).mul_left ((real_commutes c smooth).mul_left (coframe_current a)))).smul_left _

theorem coframe_commutes : Commute GaussCoframeForm.coframeAction inverseAction := by
  apply Commute.add_left
  · apply Commute.add_left
    · apply Commute.add_left
      · exact coframe_kinetic.add_left (((coframe_mixed _ _ _ _).add_left
          (coframe_mixed _ _ _ _)).add_left (coframe_mixed _ _ _ _)|>.add_left (coframe_mixed _ _ _ _))
      · apply Commute.sum_left
        intro a _
        exact ((coframe_current a).mul_left ((real_commutes _ _).mul_left (coframe_current a))).smul_left _
    · exact (((quantum_commutes _ _).mul_left (real_commutes _ _)).add_left
        ((real_commutes _ _).mul_left (quantum_commutes _ _))).smul_left _
  · exact real_commutes _ _

theorem matter_commutes : Commute GaussMatterCore.matterAction inverseAction := by
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  exact quantum_commutes _ _

theorem original_commutes : Commute GaussYukawaOperator.originalAction inverseAction := by
  exact multiplier_commutes (fun z => sourceMap (scalarField z))
    (fun _ => (sourceMap.contDiff.comp scalarField_smooth).contDiffAt)

theorem adjoint_commutes : Commute GaussFullHamiltonian.adjointAction inverseAction := by
  exact multiplier_commutes (fun z => GaussFullHamiltonian.adjointMap (scalarField z))
    (fun _ => (GaussFullHamiltonian.adjointMap.contDiff.comp scalarField_smooth).contDiffAt)

theorem gauge_momentum (v : Ambient) (hv : v.1=0) : Commute (covariantMomentum v) inverseAction := by
  change _*inverseAction=inverseAction*_
  apply LinearMap.ext
  intro f
  change covariantMomentum v (inverseAction f)=inverseAction (covariantMomentum v f)
  rw [core_commutator]
  have hK : commutatorAction v f=0 := by
    apply embed_injective
    rw [map_zero,← boundedCommutator_core,gauge_commutator_zero v hv,zero_apply]
  rw [hK,add_zero]

theorem gauge_adjoint (v : Ambient) (hv : v.1=0) : Commute (adjoint v) inverseAction :=
  paired_commutes _ _ (GaussNativeForm.adjoint_pair v) (gauge_momentum v hv)

theorem gauge_commutes : Commute gaugeKinetic inverseAction := by
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  exact (gauge_adjoint (gaugeDirection i a) rfl).mul_left
    ((real_commutes _ _).mul_left (gauge_momentum (gaugeDirection j a) rfl))

private theorem sandwich_law {R : Type*} [Ring R] (A C B S K : R)
    (hA : A*S=S*A+K) (hB : B*S=S*B+K) (hC : C*S=S*C) :
    (A*(C*B))*S = S*(A*(C*B))+(A*(C*K)+K*(C*B)) := by
  calc
    _ = A*(C*(B*S)) := by simp only [mul_assoc]
    _ = A*(C*(S*B+K)) := by rw [hB]
    _ = A*((C*S)*B+C*K) := by noncomm_ring
    _ = (A*S)*(C*B)+A*(C*K) := by rw [hC]; noncomm_ring
    _ = _ := by rw [hA]; noncomm_ring

def radialTerm (v : Ambient) : End :=
  (adjoint v).comp ((multiply GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth).comp (commutatorAction v)) +
    (commutatorAction v).comp ((multiply GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth).comp (covariantMomentum v))

theorem scalar_term (v : Ambient) :
    sandwich v v GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth*inverseAction =
      inverseAction*sandwich v v GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth+radialTerm v :=
  sandwich_law (adjoint v) (multiply _ _) (covariantMomentum v) inverseAction (commutatorAction v)
    (LinearMap.ext (adjoint_core_commutator v)) (LinearMap.ext (core_commutator v)) (real_commutes _ _).eq

def radialAction : End := (1/2 : ℂ) • ∑ a : ScalarIndex, radialTerm (scalarDirection a)

theorem scalar_commutator : scalarKinetic*inverseAction=inverseAction*scalarKinetic+radialAction := by
  simp only [scalarKinetic,radialAction,smul_mul_assoc,Finset.sum_mul,scalar_term,
    Finset.sum_add_distrib,← Finset.mul_sum,mul_smul_comm,smul_add]

theorem native_commutator : nativeAction*inverseAction=inverseAction*nativeAction+radialAction := by
  change (scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential GaussNativePotential.potential_smooth)*inverseAction = _
  rw [add_mul,add_mul,scalar_commutator,gauge_commutes.eq,(real_commutes _ _).eq]
  change _ = inverseAction*(scalarKinetic+gaugeKinetic+multiply _ _)+radialAction
  noncomm_ring

theorem diagonal_commutator : GaussDiagonalHistory.diagonalAction*inverseAction=
    inverseAction*GaussDiagonalHistory.diagonalAction+radialAction := by
  change (nativeAction+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)*inverseAction = _
  rw [add_mul,add_mul,native_commutator,coframe_commutes.eq,matter_commutes.eq]
  change _ = inverseAction*(nativeAction+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)+radialAction
  noncomm_ring

theorem full_commutator : GaussFullHamiltonian.fullAction*inverseAction=
    inverseAction*GaussFullHamiltonian.fullAction+radialAction := by
  change (GaussDiagonalHistory.diagonalAction+GaussYukawaOperator.originalAction)*inverseAction = _
  rw [add_mul,diagonal_commutator,original_commutes.eq]
  change _ = inverseAction*(GaussDiagonalHistory.diagonalAction+GaussYukawaOperator.originalAction)+radialAction
  noncomm_ring

theorem sharp_commutator : GaussFullHamiltonian.sharpAction*inverseAction=
    inverseAction*GaussFullHamiltonian.sharpAction+radialAction := by
  change (GaussDiagonalHistory.diagonalAction+GaussFullHamiltonian.adjointAction)*inverseAction = _
  rw [add_mul,diagonal_commutator,adjoint_commutes.eq]
  change _ = inverseAction*(GaussDiagonalHistory.diagonalAction+GaussFullHamiltonian.adjointAction)+radialAction
  noncomm_ring

theorem radial_form (v : Ambient) (f g : QuantumTest) :
    sourcePair f (radialTerm v g) =
      sourcePair (covariantMomentum v f) (multiply GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth (commutatorAction v g))-
      sourcePair (commutatorAction v f) (multiply GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth (covariantMomentum v g)) := by
  change inner ℂ (embed f) (embed (adjoint v (multiply GaussNativeEnergy.scalarWeight
    GaussNativeEnergy.scalarWeight_smooth (commutatorAction v g))+
    commutatorAction v (multiply GaussNativeEnergy.scalarWeight
      GaussNativeEnergy.scalarWeight_smooth (covariantMomentum v g)))) = _
  rw [map_add,inner_add_right]
  change sourcePair f (adjoint v (multiply GaussNativeEnergy.scalarWeight
    GaussNativeEnergy.scalarWeight_smooth (commutatorAction v g)))+
    sourcePair f (commutatorAction v (multiply GaussNativeEnergy.scalarWeight
      GaussNativeEnergy.scalarWeight_smooth (covariantMomentum v g))) = _
  rw [GaussNativeForm.adjoint_pair,commutatorAction_pair,sub_eq_add_neg]

theorem full_paired_radial (f g : QuantumTest) :
    sourcePair f (GaussFullHamiltonian.fullAction (inverseAction g))-
      sourcePair (inverseAction f) (GaussFullHamiltonian.fullAction g) = sourcePair f (radialAction g) := by
  have hc := LinearMap.congr_fun full_commutator g
  change GaussFullHamiltonian.fullAction (inverseAction g)=inverseAction (GaussFullHamiltonian.fullAction g)+radialAction g at hc
  rw [hc]
  change inner ℂ (embed f) (embed (_+_))-_=_
  rw [map_add,inner_add_right]
  change sourcePair f (inverseAction (GaussFullHamiltonian.fullAction g))+_-_=_
  rw [show sourcePair f (inverseAction (GaussFullHamiltonian.fullAction g)) =
    sourcePair (inverseAction f) (GaussFullHamiltonian.fullAction g) from multiply_pair reciprocal _ f _]
  abel

#print axioms coframe_commutes
#print axioms matter_commutes
#print axioms diagonal_commutator
#print axioms full_commutator
#print axioms sharp_commutator
#print axioms radial_form
#print axioms full_paired_radial
end LowEnergy.GaussRadialHamiltonian
