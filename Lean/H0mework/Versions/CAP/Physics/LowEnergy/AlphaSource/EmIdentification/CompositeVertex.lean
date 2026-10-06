import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCore
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalGradedLocalCurrent
import H0mework.Physics.LowEnergy.FullQuantum.NativeHistory.CurrentCAR

/-! Every original configuration current generates its charged composite
vertex through the complete CAR carrier. No electromagnetic direction is
supplied, and all scalar and coframe coefficients remain live. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceQuantumScalarChart GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussQuantumMultiplier CanonicalGradedCurrent
open GaussHistoryHilbert (physicalChart)
open scoped InnerProductSpace ContDiff BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance vertexModeDecision : DecidableEq Mode := LinearOrder.toDecidableEq
local instance : NormedAlgebra ℝ FiberOp := NormedAlgebra.restrictScalars ℝ ℂ _

def creationColumn (A : Matrix Mode Mode ℂ) (i : Mode) : FiberOp :=
  ∑ j : Mode, A j i • GaussCARHistory.createFiber j

def annihilationRow (A : Matrix Mode Mode ℂ) (i : Mode) : FiberOp :=
  ∑ j : Mode, A i j • GaussCARHistory.annihilateFiber j

theorem quantized_creation_column (A : Matrix Mode Mode ℂ) (i : Mode) :
    quantized A*GaussCARHistory.createFiber i-GaussCARHistory.createFiber i*quantized A = creationColumn A i := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simp only [creationColumn,sub_apply,sum_apply,smul_apply,map_sub,map_sum,map_smul]
  change LowEnergy.Fermion.quantize A (LowEnergy.Fermion.creation i (fiberCoordinates f)) -
    LowEnergy.Fermion.creation i (LowEnergy.Fermion.quantize A (fiberCoordinates f)) =
      ∑ j : Mode, A j i • LowEnergy.Fermion.creation j (fiberCoordinates f)
  simpa only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] using
    LinearMap.congr_fun (LowEnergy.FullQuantum.NativeHistory.CurrentCAR.creation_quantize A i) (fiberCoordinates f)

theorem quantized_annihilation_row (A : Matrix Mode Mode ℂ) (i : Mode) :
    quantized A*GaussCARHistory.annihilateFiber i-GaussCARHistory.annihilateFiber i*quantized A = -annihilationRow A i := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simp only [annihilationRow,sub_apply,sum_apply,smul_apply,neg_apply,map_sub,map_sum,map_smul,map_neg]
  change LowEnergy.Fermion.quantize A (LowEnergy.Fermion.annihilation i (fiberCoordinates f)) -
    LowEnergy.Fermion.annihilation i (LowEnergy.Fermion.quantize A (fiberCoordinates f)) =
      -(∑ j : Mode, A i j • LowEnergy.Fermion.annihilation j (fiberCoordinates f))
  have h := LinearMap.congr_fun (LowEnergy.Fermion.annihilation_quantize i A) (fiberCoordinates f)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] at h
  rw [←h]
  abel

def creationVertexMatrix (mu : Component) (a : NativeLie) (channel spin : Fin 2)
    (z : SourceCoordinateSlice) : FiberOp :=
  ∑ color : Fin 3, star (coefficient channel color z) •
    creationColumn (gaugeMatrix z mu a) (mode spin color)

def annihilationVertexMatrix (mu : Component) (a : NativeLie) (channel spin : Fin 2)
    (z : SourceCoordinateSlice) : FiberOp :=
  -∑ color : Fin 3, coefficient channel color z •
    annihilationRow (gaugeMatrix z mu a) (mode spin color)

theorem creation_vertex_matrix (mu : Component) (a : NativeLie) (channel spin : Fin 2)
    (z : SourceCoordinateSlice) :
    CanonicalGradedLocalCurrent.sourceCurrent mu a z *
      fiberCreation channel spin (GaussNativePotential.scalarField z) -
    fiberCreation channel spin (GaussNativePotential.scalarField z) *
      CanonicalGradedLocalCurrent.sourceCurrent mu a z = creationVertexMatrix mu a channel spin z := by
  simp only [CanonicalGradedLocalCurrent.sourceCurrent,fiberCreation,creationVertexMatrix,coefficient,
    Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro color _
  have h := congrArg
    (fun X : FiberOp => star (scalarCoefficient channel color (GaussNativePotential.scalarField z)) • X)
    (quantized_creation_column (gaugeMatrix z mu a) (mode spin color))
  simpa only [smul_sub] using h

theorem annihilation_vertex_matrix (mu : Component) (a : NativeLie) (channel spin : Fin 2)
    (z : SourceCoordinateSlice) :
    CanonicalGradedLocalCurrent.sourceCurrent mu a z *
      fiberAnnihilation channel spin (GaussNativePotential.scalarField z) -
    fiberAnnihilation channel spin (GaussNativePotential.scalarField z) *
      CanonicalGradedLocalCurrent.sourceCurrent mu a z = annihilationVertexMatrix mu a channel spin z := by
  simp only [CanonicalGradedLocalCurrent.sourceCurrent,fiberAnnihilation,annihilationVertexMatrix,coefficient,
    Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,←Finset.sum_sub_distrib,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro color _
  have h := congrArg
    (fun X : FiberOp => scalarCoefficient channel color (GaussNativePotential.scalarField z) • X)
    (quantized_annihilation_row (gaugeMatrix z mu a) (mode spin color))
  simpa only [smul_sub,smul_neg] using h

theorem creation_vertex_smooth (mu : Component) (a : NativeLie) (channel spin : Fin 2)
    (z : physicalChart) : ContDiffAt ℝ ∞ (creationVertexMatrix mu a channel spin) z.val := by
  have h : creationVertexMatrix mu a channel spin = fun w =>
      CanonicalGradedLocalCurrent.sourceCurrent mu a w *
        fiberCreation channel spin (GaussNativePotential.scalarField w) -
      fiberCreation channel spin (GaussNativePotential.scalarField w) *
        CanonicalGradedLocalCurrent.sourceCurrent mu a w :=
    funext (fun w => (creation_vertex_matrix mu a channel spin w).symm)
  rw [h]
  exact ((CanonicalGradedLocalCurrent.sourceCurrent_smooth mu a z).mul
    (creation_matrix_smooth channel spin).contDiffAt).sub
    ((creation_matrix_smooth channel spin).contDiffAt.mul
      (CanonicalGradedLocalCurrent.sourceCurrent_smooth mu a z))

theorem annihilation_vertex_smooth (mu : Component) (a : NativeLie) (channel spin : Fin 2)
    (z : physicalChart) : ContDiffAt ℝ ∞ (annihilationVertexMatrix mu a channel spin) z.val := by
  have h : annihilationVertexMatrix mu a channel spin = fun w =>
      CanonicalGradedLocalCurrent.sourceCurrent mu a w *
        fiberAnnihilation channel spin (GaussNativePotential.scalarField w) -
      fiberAnnihilation channel spin (GaussNativePotential.scalarField w) *
        CanonicalGradedLocalCurrent.sourceCurrent mu a w :=
    funext (fun w => (annihilation_vertex_matrix mu a channel spin w).symm)
  rw [h]
  exact ((CanonicalGradedLocalCurrent.sourceCurrent_smooth mu a z).mul
    (annihilation_matrix_smooth channel spin).contDiffAt).sub
    ((annihilation_matrix_smooth channel spin).contDiffAt.mul
      (CanonicalGradedLocalCurrent.sourceCurrent_smooth mu a z))

end LowEnergy.GaussComposite
