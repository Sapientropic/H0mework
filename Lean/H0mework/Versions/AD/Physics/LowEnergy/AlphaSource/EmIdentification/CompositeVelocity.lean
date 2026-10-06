import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeChargeRead
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalGradedCharge

/-! The original physical Fourier principal reads the unit charge increment
of a composite field letter on every occupation sector. The Number-one
product identity is not extended to a created Number-two state. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussQuantumMultiplier CanonicalGradedSpatialSource CanonicalGradedCharge
open scoped Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq

theorem contracted_current_column (z : SourceCoordinateSlice) (p : PhysicalMomentum)
    (spin : Fin 2) (color : Fin 3) (output : Mode) :
    contractedCurrent z p nativeY output (mode spin color) =
      -momentumMatrix z p output (mode spin color) := by
  rw [←momentum_charge]
  change (momentumMatrix z p*nativeChargeMatrix) output (mode spin color)=_
  simp only [Matrix.mul_apply,native_charge_column,mul_ite,mul_neg_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem contracted_current_row (z : SourceCoordinateSlice) (p : PhysicalMomentum)
    (spin : Fin 2) (color : Fin 3) (input : Mode) :
    contractedCurrent z p nativeY (mode spin color) input =
      -momentumMatrix z p (mode spin color) input := by
  rw [←charge_momentum]
  change (nativeChargeMatrix*momentumMatrix z p) (mode spin color) input=_
  simp only [Matrix.mul_apply,native_charge_row,ite_mul,neg_one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem current_creation_column (z : SourceCoordinateSlice) (p : PhysicalMomentum)
    (spin : Fin 2) (color : Fin 3) :
    creationColumn (contractedCurrent z p nativeY) (mode spin color) =
      -creationColumn (momentumMatrix z p) (mode spin color) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro word
  simp only [creationColumn,sum_apply,smul_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    contracted_current_column,smul_eq_mul,neg_apply,PiLp.neg_apply,neg_mul,Finset.sum_neg_distrib]

theorem current_annihilation_row (z : SourceCoordinateSlice) (p : PhysicalMomentum)
    (spin : Fin 2) (color : Fin 3) :
    annihilationRow (contractedCurrent z p nativeY) (mode spin color) =
      -annihilationRow (momentumMatrix z p) (mode spin color) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro word
  simp only [annihilationRow,sum_apply,smul_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    contracted_current_row,smul_eq_mul,neg_apply,PiLp.neg_apply,neg_mul,Finset.sum_neg_distrib]

private theorem matrix_creation (M : Matrix Mode Mode ℂ) (channel spin : Fin 2)
    (phi : Scalar) :
    quantized M*fiberCreation channel spin phi-fiberCreation channel spin phi*quantized M =
      ∑ color : Fin 3, star (scalarCoefficient channel color phi) • creationColumn M (mode spin color) := by
  simp only [fiberCreation,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro color _
  have h := congrArg (fun X : FiberOp => star (scalarCoefficient channel color phi) • X)
    (quantized_creation_column M (mode spin color))
  simpa only [smul_sub] using h

private theorem matrix_annihilation (M : Matrix Mode Mode ℂ) (channel spin : Fin 2)
    (phi : Scalar) :
    quantized M*fiberAnnihilation channel spin phi-fiberAnnihilation channel spin phi*quantized M =
      -∑ color : Fin 3, scalarCoefficient channel color phi • annihilationRow M (mode spin color) := by
  simp only [fiberAnnihilation,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ←Finset.sum_sub_distrib,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro color _
  have h := congrArg (fun X : FiberOp => scalarCoefficient channel color phi • X)
    (quantized_annihilation_row M (mode spin color))
  simpa only [smul_sub,smul_neg] using h

theorem creation_current_momentum (z : SourceCoordinateSlice) (p : PhysicalMomentum)
    (channel spin : Fin 2) (phi : Scalar) :
    quantized (contractedCurrent z p nativeY)*fiberCreation channel spin phi-
      fiberCreation channel spin phi*quantized (contractedCurrent z p nativeY) =
    -(quantized (momentumMatrix z p)*fiberCreation channel spin phi-
      fiberCreation channel spin phi*quantized (momentumMatrix z p)) := by
  rw [matrix_creation,matrix_creation]
  simp only [current_creation_column,smul_neg,Finset.sum_neg_distrib]

theorem annihilation_current_momentum (z : SourceCoordinateSlice) (p : PhysicalMomentum)
    (channel spin : Fin 2) (phi : Scalar) :
    quantized (contractedCurrent z p nativeY)*fiberAnnihilation channel spin phi-
      fiberAnnihilation channel spin phi*quantized (contractedCurrent z p nativeY) =
    -(quantized (momentumMatrix z p)*fiberAnnihilation channel spin phi-
      fiberAnnihilation channel spin phi*quantized (momentumMatrix z p)) := by
  rw [matrix_annihilation,matrix_annihilation]
  simp only [current_annihilation_row,smul_neg,Finset.sum_neg_distrib,neg_neg]

theorem creation_core_current_momentum (phi : CanonicalGradedSpatial.Localizer) (p : PhysicalMomentum)
    (channel spin : Fin 2) (f : QuantumTest) :
    currentAction phi p nativeY (creationTest channel spin f)-
      creationTest channel spin (currentAction phi p nativeY f) =
    -(CanonicalGradedSpatial.localAction phi p (creationTest channel spin f)-
      creationTest channel spin (CanonicalGradedSpatial.localAction phi p f)) := by
  apply DFunLike.ext
  intro z
  change currentAction phi p nativeY (creationTest channel spin f) z-
    (rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z)
      (currentAction phi p nativeY f z) =
    -(CanonicalGradedSpatial.localAction phi p (creationTest channel spin f) z-
      (rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z)
        (CanonicalGradedSpatial.localAction phi p f z))
  rw [currentAction_apply,currentAction_apply]
  change (phi z : ℂ) • quantized (contractedCurrent z p nativeY)
      ((rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z) (f z))-
    (rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z)
      ((phi z : ℂ) • quantized (contractedCurrent z p nativeY) (f z)) =
    -((phi z : ℂ) • quantized (momentumMatrix z p)
      ((rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z) (f z))-
    (rootVolume z : ℂ)⁻¹ • fiberCreation channel spin (GaussNativePotential.scalarField z)
      ((phi z : ℂ) • quantized (momentumMatrix z p) (f z)))
  have h := congrArg (fun T : FiberOp => (phi z : ℂ) • (rootVolume z : ℂ)⁻¹ • T (f z))
    (creation_current_momentum z p channel spin (GaussNativePotential.scalarField z))
  simpa only [sub_apply,neg_apply,mul_apply_eq_comp,map_smul,smul_sub,smul_neg,
    smul_comm (rootVolume z : ℂ)⁻¹ (phi z : ℂ)] using h

theorem creation_reader_current_momentum (phi : CanonicalGradedSpatial.Localizer) (p : PhysicalMomentum)
    (channel spin : Fin 2) (f : QuantumTest) :
    currentReader phi p nativeY (creationSource channel spin f)-
      creationSource channel spin (currentAction phi p nativeY f) =
    -(CanonicalGradedSpatial.momentumReader phi p (creationSource channel spin f)-
      creationSource channel spin (CanonicalGradedSpatial.localAction phi p f)) := by
  rw [←embed_creation_test,currentReader_core,CanonicalGradedSpatial.momentumReader_core]
  have h := congrArg embed (creation_core_current_momentum phi p channel spin f)
  simpa only [map_sub,map_neg,embed_creation_test] using h

end LowEnergy.GaussComposite
