import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaSpinClosure
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaCoefficientCommutator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaSpinNativeJet
open SaturationMonoid.PhysicsCore
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussLiveMomentum
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeMatter GaussMatterCore SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceCoframeVolume
open SourceMixedNativeReturn SourceInverseNeutralSpinCurrent SourceScalarDoubleCurrent
open SourceClockYukawaSpinClosure SourceClockYukawaSpinRelativeForm
open scoped Matrix ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem full_spin_native (j : Fin 7) (a : NativeLie) :
    Commute (GaussCoframeSpin.full j) (nativeFull a) := by
  have hp := GaussMatterCore.spin_native_commute (GaussCoframeSpin.sourceSpin j) a
  change GaussCoframeSpin.primal j*nativePrimal a=nativePrimal a*GaussCoframeSpin.primal j at hp
  have hd := congrArg (fun M : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ => M.map (starRingEnd ℂ)) hp
  rw [Matrix.map_mul,Matrix.map_mul] at hd
  change Matrix.fromBlocks (GaussCoframeSpin.primal j) 0 0
    (if j.val<3 then (GaussCoframeSpin.primal j).map (starRingEnd ℂ) else -(GaussCoframeSpin.primal j).map (starRingEnd ℂ))*
    Matrix.fromBlocks (nativePrimal a) 0 0 ((nativePrimal a).map (starRingEnd ℂ))=_
  change _=Matrix.fromBlocks (nativePrimal a) 0 0 ((nativePrimal a).map (starRingEnd ℂ))*
    Matrix.fromBlocks (GaussCoframeSpin.primal j) 0 0
      (if j.val<3 then (GaussCoframeSpin.primal j).map (starRingEnd ℂ) else -(GaussCoframeSpin.primal j).map (starRingEnd ℂ))
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero]
  apply congrArg₂ (fun A B : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ => Matrix.fromBlocks A 0 0 B) hp
  split_ifs <;> simp only [Matrix.neg_mul,Matrix.mul_neg,hd]

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem spin_fiber_native (j : Fin 7) (a : NativeLie) :
    Commute (quantized (GaussCoframeSpin.full j)) (nativeFock a) := by
  apply sub_eq_zero.mp
  change quantized (GaussCoframeSpin.full j)*quantized (nativeFull a)-
    quantized (nativeFull a)*quantized (GaussCoframeSpin.full j)=0
  rw [quantized_bracket,(full_spin_native j a).eq,sub_self]
  exact map_zero quantizer

private theorem spin_directional (j : Fin 7) (v : Ambient) :
    Commute (GaussCoframeSpin.current j) (directional v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let T := (quantized (GaussCoframeSpin.full j)).restrictScalars ℝ
  have hf : (GaussCoframeSpin.current j f : SourceCoordinateSlice → FockFiber)=T ∘ f := rfl
  have hd := T.hasFDerivAt.comp z (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  change quantized (GaussCoframeSpin.full j) (directional v f z)=directional v (GaussCoframeSpin.current j f) z
  rw [directional_apply,directional_apply,hf,hd.fderiv]
  rfl

/-- Every signed source spin current commutes with the complete native covariant momentum. -/
theorem original_spin_native_commute (j : Fin 7) (v : Ambient) :
    Commute (GaussCoframeSpin.current j) (covariantMomentum v) := by
  have hc : Commute (GaussCoframeSpin.current j) (localMultiplier (connection v) (connection_smooth v)) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z)) (spin_fiber_native j (inverseL z v).1).eq
  unfold covariantMomentum
  exact ((spin_directional j v).add_right hc).smul_right _

private theorem paired_commute (A B C : End)
    (hA : ∀ f g,sourcePair f (A g)=sourcePair (A f) g)
    (hC : ∀ f g,sourcePair f (C g)=sourcePair (B f) g) (h : Commute A B) : Commute A C := by
  apply LinearMap.ext
  intro g
  apply pair_ext
  intro f
  change sourcePair f (A (C g))=sourcePair f (C (A g))
  calc
    _=sourcePair (A f) (C g) := hA _ _
    _=sourcePair (B (A f)) g := hC _ _
    _=sourcePair (A (B f)) g := congrArg (fun x => sourcePair x g) (LinearMap.congr_fun h.eq f).symm
    _=sourcePair (B f) (A g) := (hA _ _).symm
    _=_ := (hC _ _).symm

/-- The actual density transpose and Number correction are retained through the native formal pair. -/
theorem original_spin_adjoint_native_commute (j : Fin 7) (v : Ambient) :
    Commute (GaussCoframeSpin.current j) (GaussMomentumAdjoint.adjoint v) :=
  paired_commute _ _ _ (GaussCoframeSpin.current_pair j) (GaussNativeForm.adjoint_pair v)
    (original_spin_native_commute j v)

/-- The fixed source first derivatives use exactly the same eight spin/chirality recipes as K8. -/
def constantCoefficient (sharp : Bool) (mu : Fin 8) (v : Scalar) : End :=
  if h0 : mu.val=0 then constantAction sharp v else
  if h1 : mu.val<5 then bracket (activeSpin ⟨mu.val-1,by omega⟩) (constantAction sharp v) else
    bracket (activeSpin ⟨mu.val-5,by omega⟩) (bracket (activeSpin 3) (constantAction sharp v))

private theorem commuting_jet (P J A M : End) (hc : Commute J P)
    (ha : bracket P A=(-Complex.I) • M) :
    bracket P (bracket J A)=(-Complex.I) • bracket J M := by
  have hj : bracket P (bracket J A)=bracket J (bracket P A) := by
    unfold bracket
    linear_combination (norm := noncomm_ring) A*hc.eq-hc.eq*A
  rw [hj,ha]
  simp only [bracket,mul_smul_comm,smul_mul_assoc,←smul_sub]

private theorem closure_native_jet (sharp : Bool) (mu : Fin 8) (v : Scalar) (P : End)
    (hc : ∀ j : Fin 4,Commute (activeSpin j) P)
    (hy : bracket P (fullAction sharp)=(-Complex.I) • constantAction sharp v) :
    bracket P (spinClosureCoefficient sharp mu)=(-Complex.I) • constantCoefficient sharp mu v := by
  unfold spinClosureCoefficient spinCoefficient constantCoefficient
  by_cases h0 : mu.val=0
  · simp only [h0,dif_pos]
    exact hy
  · simp only [h0]
    by_cases h1 : mu.val<5
    · simp only [h1,dif_pos]
      exact commuting_jet P (activeSpin ⟨mu.val-1,by omega⟩) (fullAction sharp) _ (hc _) hy
    · simp only [h1]
      exact commuting_jet P (activeSpin ⟨mu.val-5,by omega⟩) (spinVariation sharp 3) _ (hc _)
        (commuting_jet P (activeSpin 3) (fullAction sharp) _ (hc _) hy)

private theorem native_full_jet (sharp : Bool) (v : Ambient) :
    bracket (covariantMomentum v) (fullAction sharp)=(-Complex.I) • constantAction sharp v.1 := by
  apply LinearMap.ext
  intro f
  change covariantMomentum v (fullAction sharp f)-fullAction sharp (covariantMomentum v f)=
    (-Complex.I) • constantAction sharp v.1 f
  rw [SourceScalarGaugeForce.original_full_momentum]
  abel

/-- The inverse chart and repaired native connection cancel in all eight actual coefficient first jets. -/
theorem original_spin_closure_native_jet (sharp : Bool) (mu : Fin 8) (v : Ambient) :
    bracket (covariantMomentum v) (spinClosureCoefficient sharp mu)=
      (-Complex.I) • constantCoefficient sharp mu v.1 :=
  closure_native_jet sharp mu v.1 (covariantMomentum v)
    (fun j => original_spin_native_commute (activeIndex j) v) (native_full_jet sharp v)

/-- The complete adjoint produces the same eight source derivatives without identifying P and P†. -/
theorem original_spin_closure_adjoint_native_jet (sharp : Bool) (mu : Fin 8) (v : Ambient) :
    bracket (GaussMomentumAdjoint.adjoint v) (spinClosureCoefficient sharp mu)=
      (-Complex.I) • constantCoefficient sharp mu v.1 :=
  closure_native_jet sharp mu v.1 (GaussMomentumAdjoint.adjoint v)
    (fun j => original_spin_adjoint_native_commute (activeIndex j) v)
    (SourceYukawaCoefficientCommutator.native_full_adjoint_commutator sharp v)

end LowEnergy.SourceClockYukawaSpinNativeJet
