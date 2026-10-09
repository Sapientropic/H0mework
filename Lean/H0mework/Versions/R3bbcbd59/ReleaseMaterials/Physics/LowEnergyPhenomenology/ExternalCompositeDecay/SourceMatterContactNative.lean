import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceMatterContactCoframe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceMatterContactNative
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy GaussMatterCore
open GaussHistoryHilbert GaussLiveMomentum SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumScalarChart SourceQuantumFockGauge SourcePhysicalKineticSquare SourceScalarBalancedForce
open SourceMatterContactCoframe SourceCartanCubic GaussNativeMatter
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber

def contactMap (k : Fin 3) (z : SourceCoordinateSlice) : NativeLie →ₗ[ℝ] FiberEnd :=
  ∑ b : Fin 3,coframeGram k b z • quantumTerm b

def gramFiber (z : SourceCoordinateSlice) : FiberEnd :=
  ∑ k : Fin 3,∑ a : LieIndex,contactMap k z (lieBasis a)*contactMap k z (lieBasis a)

def gramAction : End := ∑ k : Fin 3,∑ a : LieIndex,coframeColumn k a*coframeColumn k a

private theorem contact_covariant (k : Fin 3) (z : SourceCoordinateSlice) (u v : NativeLie) :
    nativeFock u*contactMap k z v-contactMap k z v*nativeFock u=contactMap k z (nativeBracket u v) := by
  simp only [contactMap,LinearMap.sum_apply,LinearMap.smul_apply,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,←Finset.sum_sub_distrib,←smul_sub,original_matter_fiber_native]

private def rotation (u : NativeLie) (j i : LieIndex) : ℝ := inner ℝ (lieBasis j) (nativeBracket u (lieBasis i))
private theorem rotation_skew (u : NativeLie) (j i : LieIndex) : rotation u j i= -rotation u i j := by
  unfold rotation
  calc
    _=inner ℝ (nativeBracket u (lieBasis i)) (lieBasis j) := real_inner_comm _ _
    _=_ := pair_skew _ _ _

private theorem contact_rotation (k : Fin 3) (z : SourceCoordinateSlice) (u : NativeLie) (i : LieIndex) :
    contactMap k z (nativeBracket u (lieBasis i))=
      ∑ j : LieIndex,rotation u j i • contactMap k z (lieBasis j) := by
  have h := congrArg (contactMap k z) (lieBasis.sum_repr' (nativeBracket u (lieBasis i)))
  simpa only [map_sum,map_smul,rotation] using h.symm

private theorem skew_square {R : Type*} [Ring R] [Algebra ℝ R]
    {ι : Type*} [Fintype ι] (N : R) (Q : ι → R) (r : ι → ι → ℝ)
    (hr : ∀ i j,r i j= -r j i) (hN : ∀ i,N*Q i-Q i*N=∑ j,r j i • Q j) :
    Commute N (∑ i,Q i*Q i) := by
  have h (i : ι) : N*(Q i*Q i)-(Q i*Q i)*N=∑ j,r j i • (Q j*Q i+Q i*Q j) := by
    have he : N*(Q i*Q i)-(Q i*Q i)*N=(N*Q i-Q i*N)*Q i+Q i*(N*Q i-Q i*N) := by noncomm_ring
    rw [he,hN]
    simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_add,Finset.sum_add_distrib]
  have hs : (∑ i,∑ j,r j i • (Q j*Q i+Q i*Q j))=0 := by
    let S := ∑ i,∑ j,r j i • (Q j*Q i+Q i*Q j)
    have he : S= -S := by
      calc
        _=∑ j,∑ i,r j i • (Q j*Q i+Q i*Q j) := Finset.sum_comm
        _=_ := by
          simp only [S,←Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hr i j,neg_smul,add_comm (Q i*Q j)]
    have hz : (2 : ℝ) • S=0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp he
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  apply sub_eq_zero.mp
  rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  simp only [h,hs]

private theorem casimir_commute (k : Fin 3) (z : SourceCoordinateSlice) (u : NativeLie) :
    Commute (nativeFock u) (∑ i : LieIndex,contactMap k z (lieBasis i)*contactMap k z (lieBasis i)) :=
  skew_square (R := FiberEnd) (nativeFock u) (fun i => contactMap k z (lieBasis i)) (rotation u)
    (rotation_skew u) (fun i => (contact_covariant k z u (lieBasis i)).trans (contact_rotation k z u i))

/-- The full Lie-index contraction makes the original positive contact Gram invariant under every native CAR generator. -/
theorem original_contact_gram_native (z : SourceCoordinateSlice) (u : NativeLie) :
    Commute (nativeFock u) (gramFiber z) :=
  Commute.sum_right _ _ _ (fun k _ => casimir_commute k z u)

private def evaluate (z : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] FockFiber where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem original_contact_column_value (k : Fin 3) (a : LieIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    coframeColumn k a f z=contactMap k z (lieBasis a) (f z) := by
  change evaluate z (coframeColumn k a f)=_
  simp only [coframeColumn,LinearMap.sum_apply,Module.End.mul_apply,map_sum,contactMap,
    LinearMap.smul_apply,sum_apply,smul_apply]
  apply Finset.sum_congr rfl
  intro b _
  change (coframeGram k b z : ℂ) • quantumTerm b (lieBasis a) (f z)=coframeGram k b z • quantumTerm b (lieBasis a) (f z)
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

/-- The invariant fiber is the original core positive contact operator, with all coframe coefficients retained. -/
theorem original_contact_gram_value (f : QuantumTest) (z : SourceCoordinateSlice) :
    gramAction f z=gramFiber z (f z) := by
  change evaluate z (gramAction f)=_
  simp only [gramAction,LinearMap.sum_apply,Module.End.mul_apply,map_sum,gramFiber,sum_apply,mul_apply_eq_comp]
  change (∑ k : Fin 3,∑ a : LieIndex,coframeColumn k a (coframeColumn k a f) z)=_
  simp_rw [original_contact_column_value]

private theorem fiber_coframe_only (z : SourceCoordinateSlice) (s : scalarSlice × coordinateSlice) :
    gramFiber (z.1,s)=gramFiber z := rfl

private theorem directional_gram (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (gramAction f) z=gramFiber z (directional v f z) := by
  let γ : ℝ → SourceCoordinateSlice := fun t => z+t • direction v z
  have hγ : HasDerivAt γ (direction v z) 0 := by
    simpa only [γ,one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (direction v z)).const_add z
  have h0 : γ 0=z := by simp only [γ,zero_smul,add_zero]
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hγ h0.symm
  have hg := ((gramAction f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hγ h0.symm
  have hp := (gramFiber z).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0 hf
  have he : (fun t => gramAction f (γ t))=(fun t => gramFiber z (f (γ t))) := by
    funext t
    rw [original_contact_gram_value]
    have hv : (γ t).1=z.1 := by simp only [γ,direction,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
    change gramFiber ((γ t).1,(γ t).2) (f (γ t))=_
    rw [hv,fiber_coframe_only]
  change HasDerivAt (fun t => gramAction f (γ t)) _ 0 at hg
  change HasDerivAt (fun t => gramFiber z (f (γ t))) _ 0 at hp
  rw [he] at hg
  exact hg.unique hp

/-- No scalar/gauge differential direction drives this actual contact moment; its connection contribution is killed by the full source Casimir. -/
theorem original_native_momentum_commute (v : Ambient) : Commute (covariantMomentum v) gramAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional v (gramAction f) z+connection v z (gramAction f z))=
    gramAction (covariantMomentum v f) z
  rw [directional_gram,original_contact_gram_value,original_contact_gram_value]
  have h := congrArg (fun T : FiberEnd => T (f z)) (original_contact_gram_native z (inverseL z v).1).eq
  change connection v z (gramFiber z (f z))=gramFiber z (connection v z (f z)) at h
  rw [h,←map_add,←map_smul]
  rfl

private theorem fixed_pair (b : Fin 3) (a : LieIndex) (f g : QuantumTest) :
    sourcePair f (fixedContact b a g)=sourcePair (fixedContact b a f) g := by
  rw [sourcePair_integral,sourcePair_integral]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  exact GaussQuantumMultiplier.weighted_pair (fun N => GaussDensityCore.complexDensity N z)
    (matrixTerm b (lieBasis a)) (matrixTerm_hermitian b (lieBasis a)) (f z) (g z)

private theorem fixed_real (b : Fin 3) (a : LieIndex) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (fixedContact b a) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantumTerm b (lieBasis a)) (c z : ℂ) (f z)

private theorem column_pair (k : Fin 3) (a : LieIndex) (f g : QuantumTest) :
    sourcePair f (coframeColumn k a g)=sourcePair (coframeColumn k a f) g := by
  simp only [coframeColumn,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro b _
  change sourcePair f (multiply (coframeGram k b) _ (fixedContact b a g))=
    sourcePair (multiply (coframeGram k b) _ (fixedContact b a f)) g
  rw [multiply_pair,fixed_pair]
  exact congrArg (fun q => sourcePair q g) (LinearMap.congr_fun (fixed_real b a _ _).eq f)

/-- The complete contact Gram is symmetric in the original Number-weighted source pairing. -/
theorem original_contact_gram_pair (f g : QuantumTest) : sourcePair f (gramAction g)=sourcePair (gramAction f) g := by
  simp only [gramAction,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  exact (column_pair k a f (coframeColumn k a g)).trans (column_pair k a (coframeColumn k a f) g)

/-- The original complete Gram retains both independent source legs and their complex phase. -/
theorem original_contact_gram_bilinear (f g : QuantumTest) :
    sourcePair f (gramAction g)=∑ a : LieIndex,∑ k : Fin 3,
      sourcePair (coframeColumn k a f) (coframeColumn k a g) := by
  simp only [gramAction,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  exact column_pair k a f (coframeColumn k a g)

/-- This is exactly the positive contact-column energy already consumed by the original cost. -/
theorem original_contact_gram_energy (f : QuantumTest) :
    (sourcePair f (gramAction f)).re=∑ a : LieIndex,∑ k : Fin 3,‖embed (coframeColumn k a f)‖^2 := by
  have he : sourcePair f (gramAction f)=∑ k : Fin 3,∑ a : LieIndex,sourcePair (coframeColumn k a f) (coframeColumn k a f) := by
    simp only [gramAction,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro a _
    exact column_pair k a _ _
  rw [he,Finset.sum_comm]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜 := ℂ) (embed (coframeColumn k a f))

/-- The independent native adjoints preserve the same full contact invariant. -/
theorem original_native_adjoint_commute (v : Ambient) : Commute (GaussMomentumAdjoint.adjoint v) gramAction := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (gramAction g))=
    sourcePair f (gramAction (GaussMomentumAdjoint.adjoint v g))
  rw [adjoint_pair,original_contact_gram_pair,original_contact_gram_pair,adjoint_pair]
  exact congrArg (fun q => sourcePair q g) (LinearMap.congr_fun (original_native_momentum_commute v).eq f).symm

private theorem gram_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) gramAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (c z : ℂ) • gramAction f z=gramAction (multiply c hc f) z
  rw [original_contact_gram_value,original_contact_gram_value]
  exact (map_smul (gramFiber z) (c z : ℂ) (f z)).symm

private theorem mul_commutes {R : Type*} [Monoid R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A*B) C := hA.mul_left hB
attribute [local irreducible] gramAction scalarKinetic gaugeKinetic

private theorem sandwich_commute (v w : Ambient) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (sandwich v w c hc) gramAction := by
  change Commute (GaussMomentumAdjoint.adjoint v*(multiply c hc*covariantMomentum w)) gramAction
  exact mul_commutes (R := End) _ _ _ (original_native_adjoint_commute v)
    (mul_commutes (R := End) _ _ _ (gram_real c hc) (original_native_momentum_commute w))

/-- All original scalar and electric kinetic terms, and the complete real potential, exit the contact-moment evolution. -/
theorem original_native_action_commute : Commute nativeAction gramAction := by
  have hz (v w : Ambient) (c : SourceCoordinateSlice → ℝ)
      (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
      gramAction*sandwich v w c hc-sandwich v w c hc*gramAction=(0 : ℂ) • sandwich v w c hc := by
    rw [(sandwich_commute v w c hc).eq,sub_self,zero_smul]
  have hs : Commute gramAction scalarKinetic := by
    have h := SourceDilationAlgebra.homogeneous_smul (R := End) gramAction
      (∑ i : ScalarIndex,sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth)
      0 (1/2) (SourceDilationAlgebra.homogeneous_sum (R := End) gramAction _ 0
        (fun i => hz (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth))
    change gramAction*scalarKinetic=scalarKinetic*gramAction
    simpa only [scalarKinetic,zero_smul,sub_eq_zero] using h
  have hg : Commute gramAction gaugeKinetic := by
    have h := SourceDilationAlgebra.homogeneous_smul (R := End) gramAction
      (∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,sandwich (gaugeDirection i a) (gaugeDirection j a)
        (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) 0 (1/2)
      (SourceDilationAlgebra.homogeneous_sum (R := End) gramAction _ 0 (fun a =>
        SourceDilationAlgebra.homogeneous_sum (R := End) gramAction _ 0 (fun i =>
          SourceDilationAlgebra.homogeneous_sum (R := End) gramAction _ 0 (fun j =>
            hz (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)))))
    change gramAction*gaugeKinetic=gaugeKinetic*gramAction
    simpa only [gaugeKinetic,zero_smul,sub_eq_zero] using h
  have hp := (gram_real GaussNativePotential.potential GaussNativePotential.potential_smooth).eq
  change (scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential GaussNativePotential.potential_smooth)*gramAction=
    gramAction*(scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential GaussNativePotential.potential_smooth)
  simp only [add_mul,mul_add,←hs.eq,←hg.eq,hp]

open GaussDiagonalHistory

/-- The original H0 commutator is reduced to the physical coframe and local matter sectors, before any finite compression. -/
theorem original_contact_hamiltonian_current :
    diagonalAction*gramAction-gramAction*diagonalAction=
      (GaussCoframeForm.coframeAction+matterAction)*gramAction-
        gramAction*(GaussCoframeForm.coframeAction+matterAction) := by
  have h := original_native_action_commute.eq
  simp only [diagonalAction,add_mul,mul_add]
  rw [h]
  abel

end LowEnergy.SourceMatterContactNative
