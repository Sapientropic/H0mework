import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldQuantizationCore

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualFieldQuantization
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen Electromagnetic.CanonicalCoframe
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential
open GaussUnitaryHistory (HistorySpace sourceFilter inclusion)
open scoped BigOperators Matrix Matrix.Norms.L2Operator ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional
local instance : FiniteDimensional ℂ SourceMatrix := Matrix.finiteDimensional
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

abbrev HistoryOp := HistorySpace →L[ℂ] HistorySpace

def historyQuantizer : FullMatrix →L[ℂ] HistoryOp :=
  ({ toFun:=fun A=>GaussUnitaryHistory.reader (gaussQuantizer A)
     map_add':=fun A B=>by rw [map_add,GaussUnitaryHistory.reader_add]
     map_smul':=fun c A=>by rw [map_smul]; exact SourceFamilyOperator.constant_smul sourceFilter c _ } :
    FullMatrix →ₗ[ℂ] HistoryOp).toContinuousLinearMap

def fieldHistory (f : Field289) (p : PhysicalMomentum) : HistoryOp :=
  historyQuantizer (fullFieldSymbol f p)

theorem field_history_core (f : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    fieldHistory f p (inclusion (embed test))=inclusion (embed (fieldCore f p test)) := by
  change GaussUnitaryHistory.reader (fieldGauss f p) (inclusion (embed test))=_
  rw [GaussUnitaryHistory.reader_inclusion,fieldGauss_core]

theorem field_history_graph_bound (f : Field289) (p : PhysicalMomentum) :
    ‖fieldHistory f p‖≤fieldGraphBound f p := by
  apply CanonicalGradedVariation.lift_bound sourceFilter (SourceFamilyOperator.constant (fieldGauss f p))
    (fieldGraphBound f p) ((norm_nonneg _).trans (fieldGauss_graph_bound f p))
  intro F
  exact fieldGauss_graph_bound f p


theorem actual_packet_common_reader (f : Field289) (v : FullQuantum.FullSpace.FullMatterL2) :
    FullQuantum.FullSpace.fourier (fieldLeg (sourceField f) v)=ᵐ[MeasureTheory.volume]
      fun x=>YangMills.FullPairing.operator (readerMother f (FullQuantum.FullSpace.physicalMomentum x))
        (Electromagnetic.CanonicalCoframe.sourceFilter (FullQuantum.FullSpace.physicalMomentum x)
          (FullQuantum.FullSpace.fourier v x)) := by
  exact (fieldLeg_original (sourceField f) v).trans (Filter.Eventually.of_forall
    (fun x=>congrArg (fun A:FullQuantum.FullSpace.FiberOperators=>A
      (Electromagnetic.CanonicalCoframe.sourceFilter (FullQuantum.FullSpace.physicalMomentum x)
        (FullQuantum.FullSpace.fourier v x))) (native_packet_reader f _)))

private theorem affine_add (A B : Fin 4 → SourceMatrix) (p : PhysicalMomentum) :
    affineMatrix (A+B) p=affineMatrix A p+affineMatrix B p := by
  simp only [affineMatrix,Pi.add_apply,smul_add,Finset.sum_add_distrib]
  abel

private theorem affine_real_smul (A : Fin 4 → SourceMatrix) (p : PhysicalMomentum) (r : ℝ) :
    affineMatrix (r • A) p=r • affineMatrix A p := by
  simp only [affineMatrix,Pi.smul_apply,smul_add,Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

def fourierLinear (p : PhysicalMomentum) : (Fin 4 → SourceMatrix) →ₗ[ℝ] FullMatrix where
  toFun A:=realFourierMatrix A p
  map_add' A B:=by
    simp only [realFourierMatrix,affine_add]
    ext u v
    cases u <;> cases v <;>
      simp [Matrix.fromBlocks,Matrix.map_apply]
    abel
  map_smul' r A:=by
    simp only [realFourierMatrix,affine_real_smul]
    ext u v
    cases u <;> cases v <;>
      simp [Matrix.fromBlocks,Matrix.map_apply]

def densityPhase : (Fin 4 → SourceMatrix) →ₗ[ℝ] (Fin 4 → SourceMatrix) where
  toFun A:=fun i=>sourcePhaseMatrix*A i
  map_add' A B:=by funext i; exact mul_add _ _ _
  map_smul' r A:=by
    funext i
    change sourcePhaseMatrix*(r • A i)=r • (sourcePhaseMatrix*A i)
    exact mul_smul_comm _ _ _

def densityToFull (p : PhysicalMomentum) : (Fin 4 → SourceMatrix) →ₗ[ℝ] FullMatrix :=
  (fourierLinear p).comp densityPhase

def densityToHistory (p : PhysicalMomentum) : (Fin 4 → SourceMatrix) →L[ℝ] HistoryOp :=
  (historyQuantizer.restrictScalars ℝ).comp (densityToFull p).toContinuousLinearMap

theorem source_density_history (f : Field289) (p : PhysicalMomentum) :
    densityToHistory p (fieldDensityCoefficients (sourceField f))=fieldHistory f p := rfl

def historyDensityContact (f g : Field289) (p : PhysicalMomentum) : HistoryOp :=
  densityToHistory p (mixedDensityCoefficients (sourceField f) (sourceField g))

def historyShellContact (f g : Field289) (p : PhysicalMomentum) : HistoryOp :=
  densityToHistory p (shellContactCoefficients (sourceField f) (sourceField g))

theorem actual_density_contact_derivative (f g : Field289) (p : PhysicalMomentum) :
    HasDerivAt (fun t=>densityToHistory p (fun i=>densityFirstPath (sourceField f) (sourceField g) i t))
      (historyDensityContact f g p) 0 := by
  have h : HasDerivAt (fun t : ℝ=>fun i : Fin 4=>densityFirstPath (sourceField f) (sourceField g) i t)
      (mixedDensityCoefficients (sourceField f) (sourceField g)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    convert! mixedDensity_generated (sourceField f) (sourceField g) i using 1
  convert! (densityToHistory p).hasFDerivAt.comp_hasDerivAt 0 h using 1

theorem actual_shell_contact_derivative (f g : Field289) (p : PhysicalMomentum) :
    HasDerivAt (fun t=>densityToHistory p (fun i=>shellFirstPath (sourceField f) (sourceField g) i t))
      (historyShellContact f g p) 0 := by
  have h : HasDerivAt (fun t : ℝ=>fun i : Fin 4=>shellFirstPath (sourceField f) (sourceField g) i t)
      (shellContactCoefficients (sourceField f) (sourceField g)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    convert! shellContact_generated (sourceField f) (sourceField g) i using 1
  convert! (densityToHistory p).hasFDerivAt.comp_hasDerivAt 0 h using 1

theorem actual_mixed_contact_derivative (f g : Field289) (p : PhysicalMomentum) :
    HasDerivAt (fun t=>densityToHistory p (fun i=>densityFirstPath (sourceField f) (sourceField g) i t+
      shellFirstPath (sourceField f) (sourceField g) i t))
      (historyDensityContact f g p+historyShellContact f g p) 0 := by
  have derivative:=(actual_density_contact_derivative f g p).add (actual_shell_contact_derivative f g p)
  convert! derivative using 1
  funext t
  exact map_add (densityToHistory p) _ _

-- Both contacts enter with their original ordering; this is a direct insertion,
-- separate from the equal-time commutator and from the Duhamel integral.
theorem mixed_history_inclusion (f g : Field289) (p : PhysicalMomentum) (x : H) :
    (historyDensityContact f g p+historyShellContact f g p) (inclusion x)=
      inclusion ((gaussQuantizer (densityToFull p
        (mixedDensityCoefficients (sourceField f) (sourceField g)))+
        gaussQuantizer (densityToFull p (shellContactCoefficients (sourceField f) (sourceField g)))) x) := by
  change (GaussUnitaryHistory.reader _+GaussUnitaryHistory.reader _) (inclusion x)=_
  rw [←GaussUnitaryHistory.reader_add,GaussUnitaryHistory.reader_inclusion]
  rfl


open GaussComposite GaussComposite.SourceGraph

def preparedFieldRead (f : Field289) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) : ℂ :=
  SourceGraph.response (fieldHistory f p) left right lc ls rc rs u v

theorem preparedFieldRead_bound (f : Field289) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    ‖preparedFieldRead f p left right lc ls rc rs u v‖≤
      legBound^2*fieldGraphBound f p*‖u‖*‖v‖ := by
  apply (SourceGraph.response_bound _ left right lc ls rc rs u v).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (field_history_graph_bound f p) (sq_nonneg _)) (norm_nonneg u)) (norm_nonneg v)

end LowEnergy.PreparationVacuumActualFieldQuantization
