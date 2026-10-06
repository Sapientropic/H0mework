import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedSpatial

/-! The source spatial Noether current factors through its physical Fourier
principal and actual native charge on the original Number-one observation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedCharge
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussCoreHilbert
open GaussQuantumMultiplier CanonicalGradedCurrent CanonicalGradedSpatialSource
open QuantizationCheck.Fermion
open scoped Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

def chargeMatrix (a : NativeLie) : Matrix Mode Mode ℂ := Complex.I • GaussNativeMatter.nativeFull a

def contractedCurrent (z : SourceCoordinateSlice) (p : PhysicalMomentum) (a : NativeLie) :
    Matrix Mode Mode ℂ := ∑ i : Fin 3, (p i : ℂ) • gaugeMatrix z (.spatial i) a

theorem charge_temporal (z : SourceCoordinateSlice) (a : NativeLie) :
    chargeMatrix a=gaugeMatrix z .temporal a := rfl

theorem momentum_charge (z : SourceCoordinateSlice) (p : PhysicalMomentum) (a : NativeLie) :
    momentumMatrix z p*chargeMatrix a=contractedCurrent z p a := by
  simp only [momentumMatrix, chargeMatrix, contractedCurrent, gaugeMatrix,
    GaussMatterCore.matrixTerm, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    neg_mul, Finset.sum_mul, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_neg,
    Finset.sum_neg_distrib, smul_smul, Complex.ofReal_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ring

theorem charge_momentum (z : SourceCoordinateSlice) (p : PhysicalMomentum) (a : NativeLie) :
    chargeMatrix a*momentumMatrix z p=contractedCurrent z p a := by
  rw [← momentum_charge]
  simp only [chargeMatrix, momentumMatrix, mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_neg, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  rw [GaussMatterCore.boost_native_commute, mul_comm Complex.I]

def oneParticleFiber (w : Mode → ℂ) : FockFiber := fiberCoordinates.symm (oneParticle w)

theorem quantized_oneParticle (A : Matrix Mode Mode ℂ) (w : Mode → ℂ) :
    quantized A (oneParticleFiber w)=oneParticleFiber (A*ᵥw) := by
  apply fiberCoordinates.injective
  change LowEnergy.Fermion.quantize A (fiberCoordinates (fiberCoordinates.symm (oneParticle w))) =
    fiberCoordinates (fiberCoordinates.symm (oneParticle (A*ᵥw)))
  rw [fiberCoordinates.apply_symm_apply, fiberCoordinates.apply_symm_apply,
    LowEnergy.Fermion.quantize_apply, LowEnergy.Fermion.source_matrix_oneParticle]

theorem quantized_product_oneParticle (A B : Matrix Mode Mode ℂ) (w : Mode → ℂ) :
    quantized A (quantized B (oneParticleFiber w))=quantized (A*B) (oneParticleFiber w) := by
  rw [quantized_oneParticle, quantized_oneParticle, quantized_oneParticle, Matrix.mulVec_mulVec]

theorem projection_oneParticle (v : FockFiber) :
    GaussCoreLabel.fiberPiece sourceLabel v =
      oneParticleFiber (fun i => GaussCoreLabel.fiberPiece sourceLabel v {i}) := by
  apply PiLp.ext
  intro word
  change GaussCoreLabel.fiberPiece sourceLabel v word =
    oneParticle (fun i => GaussCoreLabel.fiberPiece sourceLabel v {i}) word
  by_cases singleton : ∃ i : Mode, word={i}
  · obtain ⟨i,rfl⟩ := singleton
    rw [oneParticle_singleton]
  · have hn : ∀ i : Mode, word≠{i} := by simpa only [not_exists] using singleton
    rw [oneParticle_eq_zero_of_not_singleton _ word hn, GaussCoreLabel.fiberPiece_apply]
    apply if_neg
    intro equal
    have card : word.card=1 := congrArg (fun g : NativeHistoryGrade.Label => g.1.val) equal
    exact singleton (Finset.card_eq_one.mp card)

theorem quantized_product_projection (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B*GaussCoreLabel.fiberPiece sourceLabel =
      quantized (A*B)*GaussCoreLabel.fiberPiece sourceLabel := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [mul_apply_eq_comp]
  rw [projection_oneParticle v]
  exact quantized_product_oneParticle A B _

theorem current_velocity_projection (z : SourceCoordinateSlice) (p : PhysicalMomentum) (a : NativeLie) :
    quantized (momentumMatrix z p)*quantized (chargeMatrix a)*GaussCoreLabel.fiberPiece sourceLabel =
      quantized (contractedCurrent z p a)*GaussCoreLabel.fiberPiece sourceLabel := by
  rw [quantized_product_projection, momentum_charge]

theorem actual_seed_current (z : SourceCoordinateSlice) (p : PhysicalMomentum) (a : NativeLie) :
    quantized (momentumMatrix z p) (quantized (chargeMatrix a) CanonicalCompletedSector.seed) =
      quantized (contractedCurrent z p a) CanonicalCompletedSector.seed := by
  have generated := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T CanonicalCompletedSector.seed)
    (current_velocity_projection z p a)
  simpa only [mul_apply_eq_comp, sourceLabel, canonical_seed_N1_G0] using generated

open CanonicalGradedSpatial (Localizer momentumReader)
open GaussUnitaryHistory (HistorySpace reader)
open scoped ContDiff Distributions

def chargeReader (a : NativeLie) : H →L[ℂ] H := boundedMatrix (chargeMatrix a)

theorem chargeReader_original (z : SourceCoordinateSlice) (a : NativeLie) :
    chargeReader a=gaugeReader z .temporal a := rfl

def chargeAction (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  action (fun _ => chargeMatrix a) (fun _ => contDiffAt_const)

theorem chargeReader_core (a : NativeLie) (f : QuantumTest) :
    chargeReader a (embed f)=embed (chargeAction a f) := boundedMatrix_core (chargeMatrix a) f

def currentAction (phi : Localizer) (p : PhysicalMomentum) (a : NativeLie) :
    QuantumTest →ₗ[ℂ] QuantumTest :=
  ∑ i : Fin 3, (p i : ℂ) • CanonicalGradedLocalCurrent.localAction phi (.spatial i) a

def currentReader (phi : Localizer) (p : PhysicalMomentum) (a : NativeLie) : H →L[ℂ] H :=
  ∑ i : Fin 3, (p i : ℂ) • CanonicalGradedLocalCurrent.localReader phi (.spatial i) a

theorem currentReader_core (phi : Localizer) (p : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    currentReader phi p a (embed f)=embed (currentAction phi p a f) := by
  simp only [currentReader, currentAction, sum_apply, smul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, CanonicalGradedLocalCurrent.localReader_core]

theorem currentAction_apply (phi : Localizer) (p : PhysicalMomentum) (a : NativeLie)
    (f : QuantumTest) (z : SourceCoordinateSlice) :
    currentAction phi p a f z=(phi z : ℂ) • quantized (contractedCurrent z p a) (f z) := by
  change (∑ i : Fin 3, (p i : ℂ) • ((phi z : ℂ) • quantized (gaugeMatrix z (.spatial i) a) (f z))) =
    (phi z : ℂ) • (quantizer (∑ i : Fin 3, (p i : ℂ) • gaugeMatrix z (.spatial i) a)) (f z)
  simp only [map_sum, map_smul, sum_apply, smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm (p i : ℂ) (phi z : ℂ) _

theorem core_current_velocity (phi : Localizer) (p : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    CanonicalGradedSpatial.localAction phi p (chargeAction a (GaussCoreLabel.project sourceLabel f)) =
      currentAction phi p a (GaussCoreLabel.project sourceLabel f) := by
  apply DFunLike.ext
  intro z
  rw [currentAction_apply]
  change (phi z : ℂ) • quantized (momentumMatrix z p)
    (quantized (chargeMatrix a) (GaussCoreLabel.fiberPiece sourceLabel (f z))) =
      (phi z : ℂ) • quantized (contractedCurrent z p a) (GaussCoreLabel.fiberPiece sourceLabel (f z))
  exact congrArg (fun v : FockFiber => (phi z : ℂ) • v)
    (congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z)) (current_velocity_projection z p a))

theorem currentReader_velocity (phi : Localizer) (p : PhysicalMomentum) (a : NativeLie) :
    momentumReader phi p*chargeReader a*sourceProjection=currentReader phi p a*sourceProjection := by
  apply GaussYukawaGrade.core_ext
  intro f
  simp only [mul_apply_eq_comp, sourceProjection]
  rw [← GaussCoreLabel.embed_project, chargeReader_core,
    CanonicalGradedSpatial.momentumReader_core, currentReader_core, core_current_velocity]

theorem completed_current_velocity (phi : Localizer) (p : PhysicalMomentum) (a : NativeLie) :
    reader (momentumReader phi p)*reader (chargeReader a)*historyProjection =
      reader (currentReader phi p a)*historyProjection := by
  have generated := congrArg reader (currentReader_velocity phi p a)
  simpa only [GaussUnitaryHistory.reader_mul, historyProjection] using generated

end LowEnergy.CanonicalGradedCharge
