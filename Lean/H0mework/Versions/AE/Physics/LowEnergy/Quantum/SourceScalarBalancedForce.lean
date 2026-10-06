import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarGaugeForce
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarForceBudget
import H0mework.Physics.GaugeStanding.LieRepresentation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarBalancedForce
open SaturationMonoid.PhysicsCore DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineHolonomicField StageNineDynamicBreakingVacuum SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286LinkedActiveLieRepresentation StageNineP286BracketCalculus
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussYukawaCoefficient GaussRadialDomain
open SourceCoframeVolumeCurrent SourceDilationRemainder SourceHamiltonianScaleJet SourceMixedNativeReturn
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussNativeMatter GaussQuantumMultiplier GaussNativePotential GaussMatterCore SourceCartanCubic
open SourceScalarDoubleCurrent SourceScalarGaugeForce
open scoped ContDiff InnerProductSpace BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

private theorem coordinate_bracket (a b : NativeLie) :
    p286LieBlockEmbed (p286CoordinateEquiv.symm (nativeBracket a b))=
      suLieBracket (p286LieBlockEmbed (p286CoordinateEquiv.symm a))
        (p286LieBlockEmbed (p286CoordinateEquiv.symm b)) := by
  change p286LieBlockEmbed (p286CoordinateEquiv.symm
    (p286CoordinateEquiv (p286LieBracket (p286CoordinateEquiv.symm a) (p286CoordinateEquiv.symm b))))=_
  rw [LinearEquiv.symm_apply_apply,p286LieBlockEmbed_bracket]

private theorem alg_bracket {R S : Type*} [Ring R] [Ring S] [Algebra ℂ R] [Algebra ℂ S]
    (e : R ≃ₐ[ℂ] S) (A B C : R) (h : A*B-B*A=C) : e A*e B-e B*e A=e C := by
  rw [←map_mul,←map_mul,←map_sub,h]

private theorem primal_bracket (a b : NativeLie) :
    nativePrimal a*nativePrimal b-nativePrimal b*nativePrimal a=nativePrimal (nativeBracket a b) := by
  have h : diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a))*
      diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm b))-
      diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm b))*
      diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a))=
      diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (nativeBracket a b))) := by
    rw [coordinate_bracket,diracExteriorMotherLieAction_bracket]
    rfl
  simpa only using! alg_bracket
    (R := Module.End ℂ DiracExteriorMatterCarrier)
    (S := Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ)
    LowEnergy.Quantum.operatorMatrix _ _ _ h

private theorem block_bracket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℂ) (h : A*B-B*A=C) :
    Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ))*Matrix.fromBlocks B 0 0 (B.map (starRingEnd ℂ))-
      Matrix.fromBlocks B 0 0 (B.map (starRingEnd ℂ))*Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ))=
      Matrix.fromBlocks C 0 0 (C.map (starRingEnd ℂ)) := by
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero]
  rw [sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add]
  simp only [neg_zero,add_zero]
  congr 1
  have hc := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) h
  rw [Matrix.map_sub (starRingEnd ℂ) (map_sub (starRingEnd ℂ)),Matrix.map_mul,Matrix.map_mul] at hc
  simpa only [sub_eq_add_neg] using hc

private theorem full_bracket (a b : NativeLie) :
    nativeFull a*nativeFull b-nativeFull b*nativeFull a=nativeFull (nativeBracket a b) :=
  block_bracket _ _ _ (primal_bracket a b)

private theorem left_matrix_product {R : Type*} [Ring R] (N B T U : R)
    (hB : Commute N B) (hT : N*T-T*N=U) : N*(B*T)-(B*T)*N=B*U := by
  rw [←hT]
  calc _=N*B*T-B*(T*N) := by noncomm_ring
       _=B*N*T-B*(T*N) := by rw [hB.eq]
       _=_ := by noncomm_ring

private theorem matrix_term_native (a b : NativeLie) (i : Fin 3) :
    nativeFull a*matrixTerm i b-matrixTerm i b*nativeFull a=matrixTerm i (nativeBracket a b) := by
  have hb : Commute (nativeFull a) (Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 i)) :=
    (show Commute (nativeFull a) (GaussCoframeSpin.full (Fin.castAdd 4 i)) from
      (boost_native_commute i a).symm).smul_right Complex.I
  exact left_matrix_product _ _ _ _ hb (full_bracket a b)

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

/-- Actual boost/native matrix covariance before differentiating the original connection profile. -/
theorem original_matter_fiber_native (a b : NativeLie) (i : Fin 3) :
    nativeFock a*quantumTerm i b-quantumTerm i b*nativeFock a=quantumTerm i (nativeBracket a b) := by
  change quantized (nativeFull a)*quantized (matrixTerm i b)-
    quantized (matrixTerm i b)*quantized (nativeFull a)=quantized (matrixTerm i (nativeBracket a b))
  rw [quantized_bracket,matrix_term_native]

def matterFiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  ∑ i : Fin 3,∑ b : Fin 3,(GaussMatterCore.coefficient i b z : ℂ) • quantumTerm b (connectionField z i)

def contactFiber (v : Ambient) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  ∑ i : Fin 3,∑ b : Fin 3,(GaussMatterCore.coefficient i b z : ℂ) • quantumTerm b (gaugeCoordinate i v.2)

private theorem contact_smooth (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (contactFiber v) z.val := by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro b _
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (coefficient_smooth i b z)).smul contDiffAt_const

def matterContact (v : Ambient) : CoreEnd :=
  localMultiplier (contactFiber v) (contact_smooth v)

private theorem matter_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    matterAction f z=matterFiber z (f z) := by
  simp only [matterAction,LinearMap.sum_apply,matterFiber,sum_apply,smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z))
    (map_smul quantizer (GaussMatterCore.coefficient i b z : ℂ) (matrixTerm b (connectionField z i)))

private theorem connection_inverse (z : physicalChart) (v : Ambient) (i : Fin 3) :
    nativeBracket (inverseL z.val v).1 (connectionField z.val i)+
      gaugeCoordinate i ((inverseL z.val v).2.2 : Gauge)=gaugeCoordinate i v.2 := by
  have h := congrArg (fun w : Ambient => gaugeCoordinate i w.2) (inverse_right z v)
  exact h

private theorem connection_curve (z h : SourceCoordinateSlice) (t : ℝ) (i : Fin 3) :
    connectionField (z+t • h) i=connectionField z i+t • gaugeCoordinate i (h.2.2 : Gauge) := by
  change gaugeCoordinate i ((z.2.2 : Gauge)+t • (h.2.2 : Gauge))=_
  rw [map_add,map_smul]
  rfl

private theorem coefficient_curve (z : SourceCoordinateSlice) (v : Ambient) (t : ℝ) (i b : Fin 3) :
    GaussMatterCore.coefficient i b (z+t • direction v z)=GaussMatterCore.coefficient i b z := by
  change 2*sourceTime 0*triadInverse (z.1+t • (0 : Coframe)) i b=_
  rw [smul_zero,add_zero]
  rfl

private theorem matter_curve (z : SourceCoordinateSlice) (v : Ambient) (t : ℝ) :
    matterFiber (z+t • direction v z)=matterFiber z+t • contactFiber (0,((inverseL z v).2.2 : Gauge)) z := by
  have he (i b : Fin 3) :
      (GaussMatterCore.coefficient i b (z+t • direction v z) : ℂ) •
        quantumTerm b (connectionField (z+t • direction v z) i)=
      (GaussMatterCore.coefficient i b z : ℂ) • quantumTerm b (connectionField z i)+
        t • ((GaussMatterCore.coefficient i b z : ℂ) •
          quantumTerm b (gaugeCoordinate i ((inverseL z v).2.2 : Gauge))) := by
    rw [coefficient_curve,connection_curve,map_add,map_smul,smul_add]
    exact congrArg (fun A : FockFiber →L[ℂ] FockFiber =>
      (GaussMatterCore.coefficient i b z : ℂ) • quantumTerm b (connectionField z i)+A)
      (smul_comm (GaussMatterCore.coefficient i b z : ℂ) t
        (quantumTerm b (gaugeCoordinate i ((inverseL z v).2.2 : Gauge))))
  simp only [matterFiber,he,contactFiber,Finset.sum_add_distrib,Finset.smul_sum]

private theorem affine_directional {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f h : E → V) (A B : V →L[ℝ] V) (z v : E)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ t : ℝ,h (z+t • v)=(A+t • B) (f (z+t • v))) :
    fderiv ℝ h z v=A (fderiv ℝ f z v)+B (f z) := by
  let γ : ℝ → E := fun t => z+t • v
  have hγ : HasDerivAt γ v 0 := by
    simpa only [γ,one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hγ0 : γ 0=z := by simp only [γ,zero_smul,add_zero]
  have hf0 : HasFDerivAt f (fderiv ℝ f z) (γ 0) := by rw [hγ0]; exact hf.hasFDerivAt
  have hh0 : HasFDerivAt h (fderiv ℝ h z) (γ 0) := by rw [hγ0]; exact hh.hasFDerivAt
  have hA : HasDerivAt (fun t : ℝ => A+t • B) B 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
  have hp := hA.clm_apply (hf0.comp_hasDerivAt 0 hγ)
  have he : (fun t => (A+t • B) ((f ∘ γ) t))=h ∘ γ := funext (fun t => (law t).symm)
  rw [he] at hp
  have hu := (hh0.comp_hasDerivAt 0 hγ).unique hp
  simpa only [γ,Function.comp_apply,zero_smul,add_zero,add_comm] using hu

private theorem matter_directional (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (matterAction f) z=matterFiber z (directional v f z)+
      contactFiber (0,((inverseL z v).2.2 : Gauge)) z (f z) := by
  have h := affine_directional (E := SourceCoordinateSlice) (V := FockFiber)
    f (matterAction f) (matterFiber z |>.restrictScalars ℝ)
    (contactFiber (0,((inverseL z v).2.2 : Gauge)) z |>.restrictScalars ℝ) z (direction v z)
    ((f.contDiff.differentiable (by simp)) z) (((matterAction f).contDiff.differentiable (by simp)) z)
    (fun t => by
      rw [matter_apply,matter_curve]
      rfl)
  simpa only [directional_apply,ContinuousLinearMap.coe_restrictScalars'] using! h

private theorem scaled_contact {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (N A B C : R) (c : ℂ) (h : N*A-A*N+B=C) :
    N*(c • A)-(c • A)*N+c • B=c • C := by
  rw [mul_smul_comm,smul_mul_assoc,←smul_sub,←smul_add,h]

private theorem fiber_balance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N A B C : E →L[ℂ] E) (u f : E)
    (h : N (A f)-A (N f)+B f=C f) :
    (-Complex.I) • (A u+B f+N (A f))=
      A ((-Complex.I) • (u+N f))+(-Complex.I) • C f := by
  rw [map_smul,map_add,←smul_add,←h]
  congr 1
  abel

private theorem matter_connection (z : physicalChart) (v : Ambient) :
    nativeFock (inverseL z.val v).1*matterFiber z.val-matterFiber z.val*nativeFock (inverseL z.val v).1+
      contactFiber (0,((inverseL z.val v).2.2 : Gauge)) z.val=contactFiber v z.val := by
  simp only [matterFiber,contactFiber,Finset.mul_sum,Finset.sum_mul,
    ←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  apply scaled_contact (R := FockFiber →L[ℂ] FockFiber)
  rw [original_matter_fiber_native,←map_add]
  exact congrArg (quantumTerm b) (connection_inverse z v i)

/-- The complete original matter force has no inverse-chart residual: only the actual fixed gauge direction remains. -/
theorem original_matter_momentum (v : Ambient) (f : QuantumTest) :
    covariantMomentum v (matterAction f)=matterAction (covariantMomentum v f)+(-Complex.I) • matterContact v f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have h := congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) (matter_connection ⟨z,hz⟩ v)
    change (-Complex.I) • (directional v (matterAction f) z+nativeFock (inverseL z v).1 (matterAction f z))=
      matterAction (covariantMomentum v f) z+(-Complex.I) • contactFiber v z (f z)
    rw [matter_apply,matter_apply,matter_directional]
    change nativeFock (inverseL z v).1 (matterFiber z (f z))-
      matterFiber z (nativeFock (inverseL z v).1 (f z))+
      contactFiber (0,((inverseL z v).2.2 : Gauge)) z (f z)=contactFiber v z (f z) at h
    simpa only using! fiber_balance (E := FockFiber) (nativeFock (inverseL z v).1)
      (matterFiber z) (contactFiber (0,((inverseL z v).2.2 : Gauge)) z) (contactFiber v z)
      (directional v f z) (f z) h

  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private def contactMatrix (v : Ambient) (z : SourceCoordinateSlice) : Matrix Mode Mode ℂ :=
  ∑ i : Fin 3,∑ b : Fin 3,(GaussMatterCore.coefficient i b z : ℂ) • matrixTerm b (gaugeCoordinate i v.2)

private theorem contact_quantized (v : Ambient) (z : SourceCoordinateSlice) :
    quantized (contactMatrix v z)=contactFiber v z := by
  change quantizer (contactMatrix v z)=_
  simp only [contactMatrix,contactFiber,map_sum,map_smul]
  rfl

private theorem contact_hermitian (v : Ambient) (z : SourceCoordinateSlice) :
    (contactMatrix v z).conjTranspose=contactMatrix v z := by
  simp only [contactMatrix,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
    matrixTerm_hermitian,Complex.star_def,Complex.conj_ofReal]

private theorem contact_pair (v : Ambient) (f g : QuantumTest) :
    sourcePair f (matterContact v g)=sourcePair (matterContact v f) g := by
  rw [sourcePair_integral,sourcePair_integral]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (f z))
    (contactFiber v z (g z))=
    inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (contactFiber v z (f z))) (g z)
  rw [←contact_quantized]
  exact weighted_pair (fun N => GaussDensityCore.complexDensity N z) (contactMatrix v z) (contact_hermitian v z) (f z) (g z)

/-- The independent momentum adjoint retains the same original matter contact. -/
theorem original_matter_adjoint (v : Ambient) (g : QuantumTest) :
    GaussMomentumAdjoint.adjoint v (matterAction g)=
      matterAction (GaussMomentumAdjoint.adjoint v g)+(-Complex.I) • matterContact v g := by
  apply SourceCoframeVolume.pair_ext
  intro f
  have h1 := GaussNativeForm.adjoint_pair v f (matterAction g)
  have h2 := matter_pair (covariantMomentum v f) g
  have h3 := GaussNativeForm.adjoint_pair v (matterAction f) g
  have h4 := matter_pair f (GaussMomentumAdjoint.adjoint v g)
  have h5 := contact_pair v f g
  rw [original_matter_momentum] at h3
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,map_neg,Complex.conj_I,neg_neg] at h3
  change sourcePair f (GaussMomentumAdjoint.adjoint v (matterAction g))=
    inner ℂ (embed f) (embed (matterAction (GaussMomentumAdjoint.adjoint v g)+(-Complex.I) • matterContact v g))
  rw [map_add,map_smul,inner_add_right,inner_smul_right]
  change sourcePair f (GaussMomentumAdjoint.adjoint v (matterAction g))=
    sourcePair f (matterAction (GaussMomentumAdjoint.adjoint v g))+(-Complex.I)*sourcePair f (matterContact v g)
  rw [h1,h2,h4,h5]
  change sourcePair (matterAction f) (GaussMomentumAdjoint.adjoint v g)=
    sourcePair (matterAction (covariantMomentum v f)) g+Complex.I*sourcePair (matterContact v f) g at h3
  linear_combination -h3

private theorem matrix_real (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (localMultiplier A hA) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (c z : ℂ) (f z)

private theorem matter_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute matterAction (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change matterAction (multiply c hc f) z=(c z : ℂ) • matterAction f z
  rw [matter_apply,matter_apply]
  exact map_smul (matterFiber z) (c z : ℂ) (f z)

private theorem full_real (sharp : Bool) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (SourceMixedNativeReturn.fullAction sharp) (multiply c hc) := by
  cases sharp
  · exact matrix_real (fun z => sourceMap (scalarField z))
      (fun _ => (sourceMap.contDiff.comp scalarField_smooth).contDiffAt) c hc
  · exact matrix_real (fun z => GaussFullHamiltonian.adjointMap (scalarField z))
      (fun _ => (GaussFullHamiltonian.adjointMap.contDiff.comp scalarField_smooth).contDiffAt) c hc

private theorem product_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A*B) C := hA.mul_left hB
private theorem right_product_commute {R : Type*} [Ring R] (A B C : R)
    (hB : Commute A B) (hC : Commute A C) : Commute A (B*C) := hB.mul_right hC
private theorem relative_commute {R : Type*} [Ring R] (A B : R) (m ell : ℕ) (h : Commute A B) :
    Commute A ((1-B)^(m+1)-(1-B)^(ell+1)) :=
  ((Commute.one_right A).sub_right h |>.pow_right _).sub_right
    ((Commute.one_right A).sub_right h |>.pow_right _)

private theorem gauge_X (sharp : Bool) (m ell : ℕ) (v : Ambient) (hv : v.1=0) :
    Commute (covariantMomentum v) (fullInsertion sharp m ell) :=
  right_product_commute (R := CoreEnd) _ _ _ (original_gauge_full sharp v hv)
    (relative_commute (R := CoreEnd) _ _ m ell (GaussRadialHamiltonian.gauge_momentum v hv))
private theorem gauge_adjoint_X (sharp : Bool) (m ell : ℕ) (v : Ambient) (hv : v.1=0) :
    Commute (GaussMomentumAdjoint.adjoint v) (fullInsertion sharp m ell) :=
  right_product_commute (R := CoreEnd) _ _ _ (original_gauge_full_adjoint sharp v hv)
    (relative_commute (R := CoreEnd) _ _ m ell (GaussRadialHamiltonian.gauge_adjoint v hv))

private theorem X_real (sharp : Bool) (m ell : ℕ) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (fullInsertion sharp m ell) (multiply c hc) :=
  product_commute (R := CoreEnd) _ _ _ (full_real sharp c hc)
    (relative_commute (R := CoreEnd) _ _ m ell (GaussRadialHamiltonian.real_commutes c hc)).symm

private theorem bracket_product_left {R : Type*} [Ring R] (A B X : R) :
    bracket (A*B) X=A*bracket B X+bracket A X*B := by unfold bracket; noncomm_ring
private theorem bracket_product_right {R : Type*} [Ring R] (A B X : R) :
    bracket A (B*X)=bracket A B*X+B*bracket A X := by unfold bracket; noncomm_ring
private theorem bracket_jacobi {R : Type*} [Ring R] (A M X : R) (h : Commute A X) :
    bracket A (bracket M X)=bracket (bracket A M) X := by
  have hj : bracket A (bracket M X)=bracket (bracket A M) X+bracket M (bracket A X) := by
    unfold bracket
    noncomm_ring
  have hz : bracket A X=0 := sub_eq_zero.mpr h.eq
  rw [hj,hz]
  simp only [bracket,mul_zero,zero_mul,sub_self,add_zero]
private theorem bracket_smul {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (c : ℂ) (A X : R) :
    bracket (c • A) X=c • bracket A X := by simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_zero {R : Type*} [Ring R] (A B : R) (h : Commute A B) : bracket A B=0 :=
  sub_eq_zero.mpr h.eq

private theorem first_current {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (A B W M X C D : R) (c : ℂ)
    (hAM : bracket A M=c • C) (hBM : bracket B M=c • D)
    (hAX : Commute A X) (hBX : Commute B X) (hWM : Commute W M) (hWX : Commute W X) :
    bracket (A*(W*B)) (bracket M X)=
      c • (A*(W*bracket D X)+bracket C X*(W*B)) := by
  have hW : bracket W (bracket M X)=0 := by
    rw [bracket_jacobi W M X hWX,bracket_zero W M hWM]
    simp only [bracket,zero_mul,mul_zero,sub_self]
  rw [bracket_product_left,bracket_product_left,hW,zero_mul,add_zero,
    bracket_jacobi A M X hAX,bracket_jacobi B M X hBX,hAM,hBM,bracket_smul,bracket_smul,
    mul_smul_comm,mul_smul_comm,smul_mul_assoc,←smul_add]

/-- All original gauge directions and both momentum branches remain in the first-order source current. -/
def gaugeMatterCurrent (sharp : Bool) (m ell : ℕ) : CoreEnd :=
  (-Complex.I/2 : ℂ) • ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
    (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*
          bracket (R := CoreEnd) (matterContact (gaugeDirection j a)) (fullInsertion sharp m ell))+
      bracket (R := CoreEnd) (matterContact (gaugeDirection i a)) (fullInsertion sharp m ell)*
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))

private theorem bracket_sum {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : ι → R) (X : R) :
    bracket (∑ i,A i) X=∑ i,bracket (A i) X := by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]

private theorem bracket_add {R : Type*} [Ring R] (A B X : R) :
    bracket (A+B) X=bracket A X+bracket B X := by unfold bracket; noncomm_ring

private theorem end_contact {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : Module.End ℂ V) (c : ℂ) (h : ∀ f,A (B f)=B (A f)+c • C f) :
    bracket A B=c • C := by
  apply LinearMap.ext
  intro f
  change A (B f)-B (A f)=c • C f
  rw [h f,add_sub_cancel_left]

/-- The surviving electric/matter block is the actual first-order gauge divergence, not an unestimated double derivative. -/
theorem original_mixed_current (sharp : Bool) (m ell : ℕ) :
    bracket (R := CoreEnd) electricSpatial
      (bracket (R := CoreEnd) matterAction (fullInsertion sharp m ell))=gaugeMatterCurrent sharp m ell := by
  have hX : Commute spatialAction (fullInsertion sharp m ell) :=
    (X_real sharp m ell spatialPotential spatial_smooth).symm
  have hM : Commute spatialAction matterAction := (matter_real spatialPotential spatial_smooth).symm
  have hs : bracket (R := CoreEnd) spatialAction
      (bracket (R := CoreEnd) matterAction (fullInsertion sharp m ell))=0 := by
    have h := bracket_jacobi (R := CoreEnd) spatialAction matterAction (fullInsertion sharp m ell) hX
    have hz := bracket_zero (R := CoreEnd) spatialAction matterAction hM
    exact h.trans ((congrArg (fun A : CoreEnd => bracket (R := CoreEnd) A (fullInsertion sharp m ell)) hz).trans
      (by simp only [bracket,zero_mul,mul_zero,sub_self]))
  have hg : bracket (R := CoreEnd) electricSpatial
      (bracket (R := CoreEnd) matterAction (fullInsertion sharp m ell))=
      bracket (R := CoreEnd) gaugeKinetic (bracket (R := CoreEnd) matterAction (fullInsertion sharp m ell)) :=
    (bracket_add (R := CoreEnd) gaugeKinetic spatialAction
      (bracket (R := CoreEnd) matterAction (fullInsertion sharp m ell))).trans
      ((congrArg (fun A : CoreEnd => bracket (R := CoreEnd) gaugeKinetic
        (bracket (R := CoreEnd) matterAction (fullInsertion sharp m ell))+A) hs).trans (add_zero _))
  rw [hg,gaugeKinetic,bracket_smul]
  simp only [bracket_sum]
  have he (a : LieIndex) (i j : Fin 3) :
      bracket (R := CoreEnd) (sandwich (gaugeDirection i a) (gaugeDirection j a)
        (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j))
        (bracket (R := CoreEnd) matterAction (fullInsertion sharp m ell))=
        (-Complex.I) • (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
          (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*
            bracket (R := CoreEnd) (matterContact (gaugeDirection j a)) (fullInsertion sharp m ell))+
          bracket (R := CoreEnd) (matterContact (gaugeDirection i a)) (fullInsertion sharp m ell)*
            (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) := by
    have hA : bracket (R := CoreEnd) (GaussMomentumAdjoint.adjoint (gaugeDirection i a)) matterAction=
        (-Complex.I) • matterContact (gaugeDirection i a) := by
      simpa only using! end_contact (V := QuantumTest) _ _ _ (-Complex.I) (original_matter_adjoint (gaugeDirection i a))
    have hB : bracket (R := CoreEnd) (covariantMomentum (gaugeDirection j a)) matterAction=
        (-Complex.I) • matterContact (gaugeDirection j a) := by
      simpa only using! end_contact (V := QuantumTest) _ _ _ (-Complex.I) (original_matter_momentum (gaugeDirection j a))
    simpa only using! first_current (R := CoreEnd) _ _ _ _ _ _ _ (-Complex.I) hA hB
      (gauge_adjoint_X sharp m ell _ rfl) (gauge_X sharp m ell _ rfl)
      (matter_real _ _).symm (X_real sharp m ell _ _).symm
  simp_rw [he]
  simp only [gaugeMatterCurrent,←Finset.smul_sum,smul_smul]
  congr 1
  ring

/-- The original balanced force consumes the complete source current and the Hardy subtraction together. -/
theorem actual_balanced_force_current (sharp : Bool) (m ell : ℕ) (F : GaussUnitaryHistory.Index)
    (g : diagonal.domain) :
    SourceScalarForceBudget.balancedForce sharp m ell F g=
      sourceRead F g (gaugeMatterCurrent sharp m ell-
        (2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
        (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)-
        (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-doubleProjectionFlux sharp m ell F g-
      (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F := by
  have hm := congrArg (fun A : CoreEnd =>
    sourceRead F g (A-
      (2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
      (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)-
      (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-doubleProjectionFlux sharp m ell F g)
    (original_mixed_current sharp m ell)
  have h := (actual_gapped_force_return sharp m ell F g).trans hm
  exact congrArg (fun A : GaussCoreHilbert.H →L[ℂ] GaussCoreHilbert.H =>
    A-(SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F) h

end LowEnergy.SourceScalarBalancedForce
