import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceOrderedCurrentReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLegendreCurrentReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumGaussMeasureReturn PreparationVacuumSpinGaussContraction
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier
open scoped Topology ContDiff BigOperators Matrix
abbrev SourceCurrentEnd:=QuantumTest→ₗ[ℂ] QuantumTest

theorem sourceCurrentDensityDrift_off (i : Fin 6) (direction : i=1 ∨ i=3 ∨ i=4) :
    sourceDensityDrift i=0:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  rcases direction with rfl | rfl | rfl <;>
    change ((2*sourceNumberConnection z.1 _:ℝ):ℂ) •
      (fiberNumber (f z)+(2:ℂ) • f z)=0 <;>
    simp [sourceNumberConnection]

theorem sourceCurrentAdjoint_off (i : Fin 6) (direction : i=1 ∨ i=3 ∨ i=4) :
    GaussCoframeCore.adjoint i=GaussCoframeCore.momentum i:=by
  rw [sourceCoframeAdjoint_generated,sourceCurrentDensityDrift_off i direction,smul_zero,sub_zero]

theorem sourceCurrentCoefficient_direction (i j : Fin 6)
    (direction : i=1 ∨ i=3 ∨ i=4) (distinct : i≠j) (z : physicalChart) :
    fderiv ℝ (GaussCoframeForm.currentCoefficient j) z.val (GaussCoframeCore.coframeDirection i)=0:=by
  have actual:=((GaussCoframeForm.currentCoefficient_smooth j z).differentiableAt (by simp)).hasFDerivAt
  have line:=actual.hasLineDerivAt (GaussCoframeCore.coframeDirection i)
  have constant : (fun r : ℝ=>GaussCoframeForm.currentCoefficient j
      (z.val+r • GaussCoframeCore.coframeDirection i))=
      (fun _ : ℝ=>GaussCoframeForm.currentCoefficient j z.val):=by
    funext r
    rcases direction with rfl | rfl | rfl <;>
      simp [GaussCoframeForm.currentCoefficient,GaussCoframeForm.inverseVolume,GaussNativeEnergy.volume,
        GaussCoframeCore.coframeDirection,PiLp.add_apply,PiLp.smul_apply,Ne.symm distinct]
  change HasDerivAt (fun r : ℝ=>GaussCoframeForm.currentCoefficient j
    (z.val+r • GaussCoframeCore.coframeDirection i))
      (fderiv ℝ (GaussCoframeForm.currentCoefficient j) z.val (GaussCoframeCore.coframeDirection i)) 0 at line
  rw [constant] at line
  exact line.unique (hasDerivAt_const 0 _)

private theorem sourceScalarMomentumCommute (i : Fin 6) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (zeroDerivative : ∀z : physicalChart,fderiv ℝ c z.val (GaussCoframeCore.coframeDirection i)=0) :
    Commute (GaussCoframeCore.momentum i) (GaussNativeForm.multiply c smooth):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · have hc:=Complex.ofRealCLM.hasFDerivAt.comp z
      ((smooth ⟨z,inside⟩).differentiableAt (by simp)).hasFDerivAt
    change HasFDerivAt (fun w : SourceCoordinateSlice=>(c w:ℂ)) _ z at hc
    have hf : (GaussNativeForm.multiply c smooth f : SourceCoordinateSlice→FockFiber)=
        fun w=>(c w:ℂ) • f w:=rfl
    change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)
      (GaussNativeForm.multiply c smooth f) z=
        (c z:ℂ) • ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z)
    rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,hf,
      fderiv_fun_smul hc.differentiableAt (f.contDiff.differentiable (by simp)).differentiableAt,hc.fderiv]
    change (-Complex.I) • ((c z:ℂ) • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
      (fderiv ℝ c z (GaussCoframeCore.coframeDirection i):ℂ) • f z)=_
    rw [zeroDerivative ⟨z,inside⟩,Complex.ofReal_zero,zero_smul,add_zero]
    exact smul_comm _ _ _
  · have outside (g : QuantumTest) : g z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>inside (g.tsupport_subset h))
    exact (outside _).trans (outside _).symm

theorem sourceCurrentCoefficient_momentum (i j : Fin 6)
    (direction : i=1 ∨ i=3 ∨ i=4) (distinct : i≠j) :
    Commute (GaussCoframeCore.momentum i)
      (GaussNativeForm.multiply (GaussCoframeForm.currentCoefficient j) (GaussCoframeForm.currentCoefficient_smooth j)):=
  sourceScalarMomentumCommute i _ _ (sourceCurrentCoefficient_direction i j direction distinct)

private theorem sourceSpinMomentumCommute (b : Fin 7) (i : Fin 6) :
    Commute (GaussCoframeSpin.current b) (GaussCoframeCore.momentum i):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let T:=(quantized (GaussCoframeSpin.full b)).restrictScalars ℝ
  have hf : (GaussCoframeSpin.current b f : SourceCoordinateSlice→FockFiber)=T ∘ f:=rfl
  have hd:=T.hasFDerivAt.comp z (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change quantized (GaussCoframeSpin.full b) ((-Complex.I) •
      GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z)=
    (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (GaussCoframeSpin.current b f) z
  rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,hf,hd.fderiv,map_smul]
  rfl

private theorem sourceSpinRealCommute (b : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeSpin.current b) (GaussNativeForm.multiply c smooth):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (GaussCoframeSpin.full b)) (c z:ℂ) (f z)

set_option synthInstance.maxHeartbeats 120000 in
private theorem sourceMixedMomentum (i : Fin 6) (b : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (direction : i=1 ∨ i=3 ∨ i=4)
    (commutation : Commute (GaussCoframeCore.momentum i) (GaussNativeForm.multiply c smooth)) :
    GaussCoframeForm.mixed i b c smooth=
      (GaussNativeForm.multiply c smooth*GaussCoframeSpin.current b)*GaussCoframeCore.momentum i:=by
  let C:=GaussNativeForm.multiply c smooth
  let J:=GaussCoframeSpin.current b
  let P:=GaussCoframeCore.momentum i
  change (1/2:ℂ) • (J*(C*P)+GaussCoframeCore.adjoint i*(C*J))=_
  rw [sourceCurrentAdjoint_off i direction]
  have h : P*(C*J)=(C*J)*P:=by
    rw [←mul_assoc,commutation.eq,mul_assoc,(sourceSpinMomentumCommute b i).eq.symm,←mul_assoc]
  have left : J*(C*P)=(C*J)*P:=by
    rw [←mul_assoc,(sourceSpinRealCommute b c smooth).eq]
  rw [h,left]
  module

private theorem sourceNegativeCurrent :
    GaussNativeForm.multiply (fun z=>-GaussCoframeForm.currentCoefficient 0 z)
      (fun z=>(GaussCoframeForm.currentCoefficient_smooth 0 z).neg)=
      -GaussNativeForm.multiply (GaussCoframeForm.currentCoefficient 0) (GaussCoframeForm.currentCoefficient_smooth 0):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((-GaussCoframeForm.currentCoefficient 0 z:ℝ):ℂ) • f z=
    -((GaussCoframeForm.currentCoefficient 0 z:ℂ) • f z)
  rw [Complex.ofReal_neg,neg_smul]

theorem sourceCurrentAction_single_side :
    GaussCoframeForm.currentAction=
      ∑i : Fin 6,SourceCoframeCovariantAction.currentRow i*GaussCoframeCore.momentum i:=by
  unfold GaussCoframeForm.currentAction
  rw [sourceMixedMomentum 1 5 _ _ (Or.inl rfl) (sourceCurrentCoefficient_momentum 1 0 (Or.inl rfl) (by decide)),
    sourceMixedMomentum 3 3 _ _ (Or.inr (Or.inl rfl)) (sourceCurrentCoefficient_momentum 3 1 (Or.inr (Or.inl rfl)) (by decide)),
    sourceMixedMomentum 3 4 _ _ (Or.inr (Or.inl rfl)),
    sourceMixedMomentum 4 3 _ _ (Or.inr (Or.inr rfl)) (sourceCurrentCoefficient_momentum 4 2 (Or.inr (Or.inr rfl)) (by decide))]
  · have row0 : SourceCoframeCovariantAction.currentRow 0=(0:SourceCurrentEnd):=rfl
    have row2 : SourceCoframeCovariantAction.currentRow 2=(0:SourceCurrentEnd):=rfl
    have row5 : SourceCoframeCovariantAction.currentRow 5=(0:SourceCurrentEnd):=rfl
    rw [Fin.sum_univ_six,row0,row2,row5]
    norm_num [SourceCoframeCovariantAction.currentRow,Fin.reduceFinMk,Fin.val_ofNat,Nat.reduceMod,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      sourceNegativeCurrent,mul_add,add_mul]
    module
  · rw [sourceNegativeCurrent]
    exact (sourceCurrentCoefficient_momentum 3 0 (Or.inr (Or.inl rfl)) (by decide)).neg_right

theorem sourceCanonicalLinearMomentum_original :
    sourceCanonicalLinearMomentum=GaussCoframeForm.currentAction+sourceNumberRadialMomentum:=by
  rw [sourceCanonicalLinearMomentum_split,←sourceCurrentAction_single_side]

end LowEnergy.PreparationVacuumLegendreCurrentReturn
