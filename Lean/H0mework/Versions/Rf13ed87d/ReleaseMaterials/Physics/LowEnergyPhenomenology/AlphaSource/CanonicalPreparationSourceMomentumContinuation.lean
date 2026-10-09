import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePreparedTensor

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSharedPoleCarrier
open GaussQuantumMultiplier
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussFockLabel
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge CanonicalGradedSpatialSource
open NativeHistoryGrade
open GaussGradedCompression GaussUnitaryHistory PreparationVacuumPhysicalHalfAxis
open PreparationVacuumRestModeCoupling PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open SourceQuantumConfigurationHilbert PreparationVacuumMovingPoleGaussReturn
open scoped BigOperators Matrix Topology
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℚ ℂ _

set_option maxHeartbeats 10000 in
set_option maxRecDepth 128 in
private theorem sharedCompression_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D : Submodule ℂ E) (A B : D→ₗ[ℂ] E) (F : Finset D) (x : E) :
    FiniteCoreEvolution.compression ({domain:=D,toFun:=A}:E→ₗ.[ℂ] E) F x=
      ((FiniteCoreEvolution.coreSpan ({domain:=D,toFun:=B}:E→ₗ.[ℂ] E) F).orthogonalProjectionOnto
        (A ⟨((FiniteCoreEvolution.coreSpan ({domain:=D,toFun:=B}:E→ₗ.[ℂ] E) F).orthogonalProjectionOnto x:E),
          FiniteCoreEvolution.coreSpan_le ({domain:=D,toFun:=B}:E→ₗ.[ℂ] E) F ((FiniteCoreEvolution.coreSpan ({domain:=D,toFun:=B}:E→ₗ.[ℂ] E) F).orthogonalProjectionOnto x).property⟩):E):=by
  rfl

private def fixedCompressionLinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D : Submodule ℂ E) (F : Finset D) : (D→ₗ[ℂ] E)→ₗ[ℂ] (E→L[ℂ] E) where
  toFun := fun A=>FiniteCoreEvolution.compression ({domain:=D,toFun:=A}:E→ₗ.[ℂ] E) F
  map_add' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    rw [add_apply,sharedCompression_apply D (A+B) 0 F x,sharedCompression_apply D A 0 F x,sharedCompression_apply D B 0 F x]
    simp only [LinearMap.add_apply,map_add,Submodule.coe_add]
  map_smul' := by
    intro c A
    apply ContinuousLinearMap.ext
    intro x
    rw [smul_apply,sharedCompression_apply D (c • A) 0 F x,sharedCompression_apply D A 0 F x]
    simp only [LinearMap.smul_apply,map_smul,Submodule.coe_smul,RingHom.id_apply]

private def realizedCoreLinear : (QuantumTest→ₗ[ℂ] QuantumTest)→ₗ[ℂ] (Core→ₗ[ℂ] H) where
  toFun := fun A=>GaussCoreHilbert.embed.comp (A.comp GaussCoreHilbert.coreEquiv.symm.toLinearMap)
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply,LinearMap.add_apply,map_add]
  map_smul' := by
    intro c A
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,map_smul,RingHom.id_apply]

private def coreCompressionLinear (F : GaussUnitaryHistory.Index) : (QuantumTest→ₗ[ℂ] QuantumTest)→ₗ[ℂ] (H→L[ℂ] H):=
  (fixedCompressionLinear Core F).comp realizedCoreLinear

private def gradedCompressionLinear (F : GaussUnitaryHistory.Index) : (QuantumTest→ₗ[ℂ] QuantumTest)→ₗ[ℂ] (H→L[ℂ] H) where
  toFun := fun A=>∑g : Label,projection g*coreCompressionLinear F A*projection g
  map_add' := by intro A B;simp only [map_add,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' := by intro c A;simp only [map_smul,mul_smul_comm,smul_mul_assoc,Finset.smul_sum,RingHom.id_apply]

def sourceMomentumLinear : PhysicalMomentum→ₗ[ℝ] (QuantumTest→ₗ[ℂ] QuantumTest) where
  toFun := CanonicalPhysicalSpatial.momentumAction
  map_add' := by
    intro p k
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change quantizer (momentumMatrix z (p+k)) (f z)=quantizer (momentumMatrix z p) (f z)+quantizer (momentumMatrix z k) (f z)
    rw [momentumMatrix_add,map_add,add_apply]
  map_smul' := by
    intro r p
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change quantizer (momentumMatrix z (r • p)) (f z)=r • (quantizer (momentumMatrix z p) (f z))
    rw [momentumMatrix_smul,map_smul,smul_apply]
    rfl

def sourceVelocityLinear (F : GaussUnitaryHistory.Index) : PhysicalMomentum→ₗ[ℝ] (H→L[ℂ] H):=
  (gradedCompressionLinear F).restrictScalars ℝ |>.comp sourceMomentumLinear

theorem actualC_affine (F : GaussUnitaryHistory.Index) (p : PhysicalMomentum) :
    actualC p F=actualC 0 F+sourceVelocityLinear F p:=by
  have origin : actualC 0 F=gradedCompressionLinear F diagonalAction:=
    (show actualC 0 F=gradedCompressionLinear F (CanonicalPhysicalSpatial.physicalAction 0) from rfl).trans
      (congrArg (gradedCompressionLinear F) CanonicalPhysicalSpatial.physicalAction_zero)
  calc
    _=gradedCompressionLinear F (diagonalAction+CanonicalPhysicalSpatial.momentumAction p):=rfl
    _=gradedCompressionLinear F diagonalAction+gradedCompressionLinear F (CanonicalPhysicalSpatial.momentumAction p):=
      map_add (gradedCompressionLinear F) _ _
    _= _:=congrArg₂ HAdd.hAdd origin.symm rfl

def sourceVelocity (F : GaussUnitaryHistory.Index) : PhysicalMomentum→L[ℝ] (H→L[ℂ] H):=
  (sourceVelocityLinear F).toContinuousLinearMap

theorem actualC_continuous (F : GaussUnitaryHistory.Index) : Continuous (fun p : PhysicalMomentum=>actualC p F):=by
  rw [show (fun p : PhysicalMomentum=>actualC p F)=(fun p=>actualC 0 F+sourceVelocityLinear F p) from funext (actualC_affine F)]
  exact continuous_const.add (sourceVelocity F).continuous

theorem actualC_difference_price (F : GaussUnitaryHistory.Index) (p k : PhysicalMomentum) :
    ‖actualC p F-actualC k F‖ ≤ ‖sourceVelocity F‖*‖p-k‖:=by
  rw [actualC_affine F p,actualC_affine F k]
  have difference : actualC 0 F+sourceVelocityLinear F p-(actualC 0 F+sourceVelocityLinear F k)=sourceVelocity F (p-k):=by
    simp only [map_sub,sourceVelocity]
    abel
  rw [difference]
  exact (sourceVelocity F).le_opNorm (p-k)

theorem sourceResolvent_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    Continuous (fun p : PhysicalMomentum=>CanonicalPhysicalResolvent.finiteResolvent p F z):=by
  change Continuous (fun p : PhysicalMomentum=>Ring.inverse (actualC p F-z • 1))
  apply continuous_iff_continuousAt.mpr
  intro p
  have unit:=FullYSourceResolventGraphSplice.resolvent_isUnit (actualC p F) (actualC_symmetric p F) z nonreal
  have inverse : ContinuousAt Ring.inverse (actualC p F-z • 1):=by
    rcases unit with ⟨u,hu⟩
    rw [←hu]
    exact NormedRing.inverse_continuousAt u
  have inner : ContinuousAt (fun k : PhysicalMomentum=>actualC k F-z • 1) p:=
    (actualC_continuous F).continuousAt.sub continuousAt_const
  exact inverse.tendsto.comp inner.tendsto

theorem sourceResolvent_difference_price (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0)
    (p k : PhysicalMomentum) :
    ‖CanonicalPhysicalResolvent.finiteResolvent p F z-CanonicalPhysicalResolvent.finiteResolvent k F z‖ ≤
      (1/|z.im|)^2*‖sourceVelocity F‖*‖p-k‖:=by
  have left : CanonicalPhysicalResolvent.finiteResolvent p F z*(actualC p F-z • 1)=1:=
    FullYSourceResolventGraphSplice.resolvent_left (actualC p F) (actualC_symmetric p F) z nonreal
  have right : (actualC k F-z • 1)*CanonicalPhysicalResolvent.finiteResolvent k F z=1:=
    FullYSourceResolventGraphSplice.resolvent_right (actualC k F) (actualC_symmetric k F) z nonreal
  have difference : CanonicalPhysicalResolvent.finiteResolvent p F z-CanonicalPhysicalResolvent.finiteResolvent k F z=
      CanonicalPhysicalResolvent.finiteResolvent p F z*(actualC k F-actualC p F)*CanonicalPhysicalResolvent.finiteResolvent k F z:=by
    calc
      _=CanonicalPhysicalResolvent.finiteResolvent p F z*((actualC k F-z • 1)*CanonicalPhysicalResolvent.finiteResolvent k F z)-
          (CanonicalPhysicalResolvent.finiteResolvent p F z*(actualC p F-z • 1))*CanonicalPhysicalResolvent.finiteResolvent k F z:=by
        rw [left,right,mul_one,one_mul]
      _= _:=by simp only [mul_sub,sub_mul,mul_assoc];abel
  have delta:=actualC_difference_price F k p
  rw [norm_sub_rev k p] at delta
  have boundP:=CanonicalPhysicalResolvent.finite_bound p F z nonreal
  have boundK:=CanonicalPhysicalResolvent.finite_bound k F z nonreal
  rw [difference]
  calc
    _ ≤ (‖CanonicalPhysicalResolvent.finiteResolvent p F z‖*‖actualC k F-actualC p F‖)*‖CanonicalPhysicalResolvent.finiteResolvent k F z‖:=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((1/|z.im|)*(‖sourceVelocity F‖*‖p-k‖))*(1/|z.im|):=by gcongr
    _= _:=by ring

theorem sourceTime_continuous (F : GaussUnitaryHistory.Index) :
    Continuous (fun pt : PhysicalMomentum×ℝ=>SourceFiniteUnitary.time (actualC pt.1 F) pt.2):=by
  unfold SourceFiniteUnitary.time
  exact NormedSpace.exp_continuous.comp (continuous_snd.smul
    ((actualC_continuous F).comp continuous_fst |>.const_smul (-Complex.I)))

theorem sourceModeKernel_continuous (q : PhysicalResponsePoint) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>sourceModeKernel q x.1 x.2.1 x.2.2):=by
  have leftInput : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>(x.1,-x.2.2)):=
    continuous_fst.prodMk continuous_snd.snd.neg
  have rightInput : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>(x.2.1,x.2.2)):=
    continuous_snd.fst.prodMk continuous_snd.snd
  have leftTime:=(sourceTime_continuous q.F).comp leftInput
  have rightTime:=(sourceTime_continuous q.F).comp rightInput
  have leftR:=(sourceResolvent_continuous q.F q.z nonrealL).comp
    (continuous_fst : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>x.1))
  have rightR:=(sourceResolvent_continuous q.F q.w nonrealR).comp
    (continuous_snd.fst : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>x.2.1))
  exact (((leftTime.mul leftR).mul continuous_const).mul rightR).mul rightTime

/-- The entire actual tensor has a source-generated continuous return to the common carrier, without any continuity assertion about eigenvector labels. -/
theorem actualModeTensor_continuous (q : PhysicalResponsePoint) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>
      movingOverlap x.1*actualModeTensor q x.1 x.2.1 x.2.2*(movingOverlap x.2.1).conjTranspose):=by
  simp only [actualModeTensor_same_carrier q _ _ _ nonrealL nonrealR]
  apply continuous_pi
  intro left
  apply continuous_pi
  intro right
  exact ((sourcePoleRead q.epsilon q.precision 0 0 left right).continuous.comp
    (sourceModeKernel_continuous q nonrealL nonrealR)).neg

theorem movingOverlap_zero : movingOverlap (0:PhysicalMomentum)=1:=by
  ext left right
  exact sourceMovingPole_orthonormal 0 left right

/-- The actual finite-window current is integrated after its exact bilateral return, retaining the full eight-by-eight tensor. -/
theorem actualModeWindow_continuous (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>fun left right : RestStateIndex=>
      ∫t in (0:ℝ)..T,PreparationVacuumGaugeSourceInjection.laplaceWeight lambda t*
        (movingOverlap p.1*actualModeTensor q p.1 p.2 t*(movingOverlap p.2).conjTranspose) left right):=by
  have args : Continuous (fun x : (PhysicalMomentum×PhysicalMomentum)×ℝ=>(x.1.1,x.1.2,x.2)):=
    continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)
  have whole:=(actualModeTensor_continuous q nonrealL nonrealR).comp args
  apply continuous_pi
  intro left
  apply continuous_pi
  intro right
  have entry:= (continuous_apply right).comp ((continuous_apply left).comp whole)
  have weight : Continuous (fun x : (PhysicalMomentum×PhysicalMomentum)×ℝ=>
      PreparationVacuumGaugeSourceInjection.laplaceWeight lambda x.2):=by
    unfold PreparationVacuumGaugeSourceInjection.laplaceWeight
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (weight.mul entry) 0 T

end LowEnergy.PreparationVacuumSharedPoleCarrier
