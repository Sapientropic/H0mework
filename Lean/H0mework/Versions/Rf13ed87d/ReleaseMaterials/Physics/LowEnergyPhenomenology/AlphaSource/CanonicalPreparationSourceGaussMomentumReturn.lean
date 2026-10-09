import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussMeasureJets

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumGaussMeasureReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSpinGaussContraction PreparationVacuumSpinCarReturn
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussScalarTransport
open GaussQuantumMultiplier GaussFockPair
open PreparationVacuumCoframeQuantumCurrent PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumGravityLegendreSource
open scoped Topology ContDiff BigOperators Matrix

theorem sourceNumberConnection_smooth (j : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice=>sourceNumberConnection w.1 j) z.val:=by
  have volumeNonzero := (GaussNativeEnergy.volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5≠0 at volumeNonzero
  have q0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp volumeNonzero).1).1
  have q2 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp volumeNonzero).1).2
  have q5 := (mul_ne_zero_iff.mp volumeNonzero).2
  fin_cases j
  · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice=>1/(2*w.1 0)) z.val
    fun_prop (disch:=aesop)
  · exact contDiffAt_const
  · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice=>1/(2*w.1 2)) z.val
    fun_prop (disch:=aesop)
  · exact contDiffAt_const
  · exact contDiffAt_const
  · change ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice=>1/(2*w.1 5)) z.val
    fun_prop (disch:=aesop)

def sourceDensityDrift (j : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  localMultiplier
    (fun z=>((2*sourceNumberConnection z.1 j:ℝ):ℂ) •
      (fiberNumber+(2:ℂ) • ContinuousLinearMap.id ℂ FockFiber))
    (fun z=>(Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
      (contDiffAt_const.mul (sourceNumberConnection_smooth j z))).smul contDiffAt_const)

theorem sourceDensityDrift_apply (j : Fin 6) (f : QuantumTest)
    (z : SourceCoordinateSlice) (word : Occupation) :
    sourceDensityDrift j f z word=
      ((2*(word.card+2:ℝ)*sourceNumberConnection z.1 j):ℂ)*f z word:=by
  change ((2*sourceNumberConnection z.1 j:ℝ):ℂ)*
    (fiberNumber (f z) word+2*f z word)=_
  rw [fiberNumber_apply]
  push_cast
  ring

theorem sourceTranspose_generated (j : Fin 6) :
    GaussCoframeCore.transpose (GaussCoframeCore.coframeDirection j)=
      -GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection j)-sourceDensityDrift j:=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  rw [GaussCoframeCore.transpose_embed]
  apply PiLp.ext
  intro word
  change scalarLp word.card
      (GaussDensityCore.weightedTranspose word.card (GaussCoframeCore.coframeDirection j) (component word f))=
    scalarLp word.card (component word
      ((-GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection j)-sourceDensityDrift j) f))
  apply congrArg (scalarLp word.card)
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · rw [sourceWeightedTranspose_generated word.card j (component word f) ⟨z,inside⟩]
    rw [←GaussDensityCore.derivative_apply,←GaussCoframeCore.component_derivative]
    change -(GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection j) f z word)-
      ((2*(word.card+2:ℝ)*sourceNumberConnection z.1 j):ℂ)*f z word=_
    rw [←sourceDensityDrift_apply]
    rfl
  · have outside (g : GaussDensityCore.ScalarTest) : g z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>inside (g.tsupport_subset h))
    exact (outside _).trans (outside _).symm

theorem sourceCoframeAdjoint_generated (j : Fin 6) :
    GaussCoframeCore.adjoint j=GaussCoframeCore.momentum j-Complex.I • sourceDensityDrift j:=by
  rw [GaussCoframeCore.adjoint,sourceTranspose_generated,GaussCoframeCore.momentum]
  module

def sourceNumberScalarAction (j : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  localMultiplier (fun z=>(sourceNumberConnection z.1 j:ℂ) • fiberNumber)
    (fun z=>(Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
      (sourceNumberConnection_smooth j z)).smul contDiffAt_const)

def sourceGeometryScalarAction (j : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussNativeForm.multiply (fun z=>sourceNumberConnection z.1 j) (sourceNumberConnection_smooth j)

theorem sourceDensityDrift_split (j : Fin 6) :
    sourceDensityDrift j=(2:ℂ) • sourceNumberScalarAction j+(4:ℂ) • sourceGeometryScalarAction j:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((2*sourceNumberConnection z.1 j:ℝ):ℂ) •
    (fiberNumber (f z)+(2:ℂ) • f z)=
      (2:ℂ) • ((sourceNumberConnection z.1 j:ℂ) • fiberNumber (f z))+
        (4:ℂ) • ((sourceNumberConnection z.1 j:ℂ) • f z)
  simp only [smul_add,smul_smul,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  module

-- Right/left are the original Gram action readouts, without an identification of independent π.
def sourceNoetherMomentumRight (j : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussCoframeCore.momentum j-Complex.I • sourceNumberScalarAction j+
    SourceCoframeCovariantAction.connectionAction j

def sourceNoetherMomentumLeft (j : Fin 6) : QuantumTest→ₗ[ℂ] QuantumTest:=
  GaussCoframeCore.adjoint j+Complex.I • sourceNumberScalarAction j+
    SourceCoframeCovariantAction.connectionAction j

theorem sourceNoetherMomentumRight_source (field : Field289) (f : QuantumTest)
    (z : physicalChart) (j : Fin 6) :
    sourceNoetherMomentumRight j f z.val=GaussCoframeCore.momentum j f z.val-
      (∑i : LorentzIndex,(sourceShiftWeight z.val j i:ℂ) •
        sourceSpinFiber (field,z.val) (sourceState z.val) i) (f z.val):=by
  rw [sourceGaussSpinShift_return]
  have number : sourceNumberScalarAction j f z.val=
      (sourceNumberConnection z.val.1 j:ℂ) • fiberNumber (f z.val):=rfl
  have connection : SourceCoframeCovariantAction.connectionAction j f z.val=
      SourceCoframeSpinConnection.connectionFiber j z.val (f z.val):=rfl
  change GaussCoframeCore.momentum j f z.val-Complex.I • (sourceNumberScalarAction j f z.val)+
      SourceCoframeCovariantAction.connectionAction j f z.val=_
  rw [number,connection]
  simp only [sub_apply,smul_apply,smul_smul]
  module

theorem sourceNoetherMomentum_geometry (j : Fin 6) :
    sourceNoetherMomentumLeft j-sourceNoetherMomentumRight j=
      (-4*Complex.I) • sourceGeometryScalarAction j:=by
  rw [sourceNoetherMomentumLeft,sourceNoetherMomentumRight,sourceCoframeAdjoint_generated,
    sourceDensityDrift_split]
  module

end LowEnergy.PreparationVacuumGaussMeasureReturn
