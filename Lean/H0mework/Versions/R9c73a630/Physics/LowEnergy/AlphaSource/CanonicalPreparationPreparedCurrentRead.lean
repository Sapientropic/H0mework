import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationFullDensityCurrent

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPreparedCurrent
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDensityCore
open GaussComposite GaussComposite.SourceGraph
open PreparationVacuumNativeClosure PreparationVacuumWeylDomain PreparationChartGuard
open CanonicalPreparationCore.Completed CanonicalScalarPreparation
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumFieldConstraintResponse
open GaussUnitaryHistory (Index sourceFilter inclusion)
open CanonicalGradedSpatialSource
open Set Filter Topology
open scoped ContDiff Topology InnerProductSpace LinearPMap
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

def coveredTest : QuantumTest →ₗ[ℂ] QuantumTest :=
  scalarMultiplier (fun z => (sourceCover z : ℂ))
    (Complex.ofRealCLM.contDiff.comp sourceCover.contDiff)

theorem covered_current_core (f : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    embed (familyCore f p (coveredTest test))=localizedGauss f p sourceCover (embed test) := by
  rw [localizedGauss_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  exact (fiberFamily f p z).map_smul (sourceCover z:ℂ) (test z)

def finiteCurrent (f : Field289) (p : PhysicalMomentum) (F : Index) (x : H) : H :=
  embed (familyCore f p (coveredTest (sourceTestApprox F x)))

theorem finiteCurrent_exact (f : Field289) (p : PhysicalMomentum) (F : Index) (x : H) :
    finiteCurrent f p F x=localizedGauss f p sourceCover (sourceApprox F x) := by
  rw [finiteCurrent,covered_current_core,sourceTestApprox_embed]

theorem original_current_samefilter (f : Field289) (p : PhysicalMomentum) (x : localCarrier) :
    Tendsto (fun F : Index=>finiteCurrent f p F x.val) sourceFilter (𝓝 (fullCurrent f p x)) := by
  simp only [finiteCurrent,covered_current_core]
  exact (localizedGauss f p sourceCover).continuous.tendsto x.val |>.comp (same_source_approximation x.val)

theorem sourceApprox_contractive (F : Index) (x : H) : ‖sourceApprox F x‖ ≤ ‖x‖ := by
  have each (g : NativeHistoryGrade.Label) :
      ‖NativeHistoryGrade.projection g
        ((FiniteCoreEvolution.coreSpan GaussDiagonalHistory.diagonal F).starProjection
          (NativeHistoryGrade.projection g x))‖ ≤ ‖NativeHistoryGrade.projection g x‖ :=
    (NativeHistoryGrade.piece_bound g _).trans
      ((FiniteCoreEvolution.coreSpan GaussDiagonalHistory.diagonal F).norm_starProjection_apply_le _)
  have squared : ‖sourceApprox F x‖^2 ≤ ‖x‖^2 := by
    rw [sourceApprox_apply,NativeHistoryGrade.norm_sum_projection,←NativeHistoryGrade.norm_resolution x]
    exact Finset.sum_le_sum (fun g _=>pow_le_pow_left₀ (norm_nonneg _) (each g) 2)
  nlinarith [norm_nonneg (sourceApprox F x),norm_nonneg x]

theorem finiteCurrent_uniform (f : Field289) (p : PhysicalMomentum) (F : Index) (x : localCarrier) :
    ‖finiteCurrent f p F x.val‖ ≤
      currentPrice f p*‖x‖ := by
  rw [finiteCurrent_exact]
  exact ((localizedGauss f p sourceCover).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (localizedGauss_norm f p sourceCover) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (sourceApprox_contractive F x.val) (currentPrice_nonnegative f p)))

def preparedCurrent (f : Field289) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (x y : sourceLocalSpace) : ℂ :=
  inner ℂ (legPoint left lc ls x).val (fullCurrent f p (legPoint right rc rs y))

theorem preparedCurrent_original (f : Field289) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (x y : sourceLocalSpace) :
    preparedCurrent f p left right lc ls rc rs x y=
      preparedFamilyRead f p sourceCover left right lc ls rc rs
        (zeroLocalizedProfile actualNativeLocalizer x) (zeroLocalizedProfile actualNativeLocalizer y) := by
  unfold preparedFamilyRead SourceGraph.response familyHistory
  rw [GaussUnitaryHistory.reader_inclusion,inclusion.inner_map_map]
  rfl

theorem preparedCurrent_bound (f : Field289) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (x y : sourceLocalSpace) :
    ‖preparedCurrent f p left right lc ls rc rs x y‖ ≤
      (legBound*CanonicalScalarPreparation.localBound (outerCutoff actualNativeLocalizer)*‖x‖)*
        (currentPrice f p*(legBound*CanonicalScalarPreparation.localBound
          (outerCutoff actualNativeLocalizer)*‖y‖)) := by
  apply (norm_inner_le_norm (𝕜:=ℂ) _ _).trans
  apply mul_le_mul (sourceLeg_bound left lc ls x) _ (norm_nonneg _)
    (mul_nonneg (mul_nonneg legBound_nonnegative
      (CanonicalScalarPreparation.localBound_nonnegative _)) (norm_nonneg x))
  exact (fullCurrent_bound f p (legPoint right rc rs y)).trans
    (mul_le_mul_of_nonneg_left (sourceLeg_bound right rc rs y) (currentPrice_nonnegative f p))

theorem preparedCurrent_samefilter (f : Field289) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (x y : sourceLocalSpace) :
    Tendsto (fun F : Index=>inner ℂ
      (embed (sourceTestApprox F (sourceLeg left lc ls x)))
      (finiteCurrent f p F (sourceLeg right rc rs y))) sourceFilter
      (𝓝 (preparedCurrent f p left right lc ls rc rs x y)) :=
  (same_source_approximation (sourceLeg left lc ls x)).inner
    (original_current_samefilter f p (legPoint right rc rs y))

private theorem add_i_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : E →L[ℂ] E) (a b : ℝ) (ha : ‖A‖ ≤ a) (hb : ‖B‖ ≤ b) :
    ‖A+Complex.I • B‖ ≤ a+b := by
  apply (norm_add_le A (Complex.I • B)).trans
  rw [norm_smul,Complex.norm_I,one_mul]
  exact add_le_add ha hb

private theorem commutator_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : E →L[ℂ] E) (a b : ℝ) (ha : ‖A‖ ≤ a) (hb : ‖B‖ ≤ b)
    (hpa : 0 ≤ a) (hpb : 0 ≤ b) : ‖A*B-B*A‖ ≤ 2*a*b := by
  apply (norm_sub_le (A*B) (B*A)).trans
  calc
    _ ≤ ‖A‖*‖B‖+‖B‖*‖A‖ := add_le_add (norm_mul_le A B) (norm_mul_le B A)
    _ ≤ a*b+b*a := add_le_add (mul_le_mul ha hb (norm_nonneg _) hpa)
      (mul_le_mul hb ha (norm_nonneg _) hpb)
    _=_ := by ring

-- The original 36×289 reader is unchanged; the two physical momenta remain independent.
def curvatureDensityCurrent (k : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum) :
    localCarrier →L[ℂ] localCarrier :=
  current (readerReal k row) p+Complex.I • current (readerImag k row) p

def curvaturePrice (k : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum) : ℝ :=
  currentPrice (readerReal k row) p+currentPrice (readerImag k row) p

theorem curvatureDensityCurrent_norm (k : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum) :
    ‖curvatureDensityCurrent k row p‖ ≤ curvaturePrice k row p := by
  exact add_i_norm (current (readerReal k row) p) (current (readerImag k row) p)
    (currentPrice (readerReal k row) p) (currentPrice (readerImag k row) p)
    (current_norm _ _) (current_norm _ _)

theorem curvatureDensityCurrent_core (k : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum)
    (test : QuantumTest) :
    (curvatureDensityCurrent k row p (localCoreMap test)).val=
      embed (familyCore (readerReal k row) p (sourceCut test))+
        Complex.I • embed (familyCore (readerImag k row) p (sourceCut test)) := by
  change fullCurrent (readerReal k row) p (localCoreMap test)+
    Complex.I • fullCurrent (readerImag k row) p (localCoreMap test)=_
  rw [fullCurrent_core,fullCurrent_core]

def curvatureDensityPrepared (k : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (x y : sourceLocalSpace) : ℂ :=
  inner ℂ (legPoint left lc ls x) (curvatureDensityCurrent k row p (legPoint right rc rs y))

theorem curvatureDensityPrepared_original (k : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (x y : sourceLocalSpace) :
    curvatureDensityPrepared k row p left right lc ls rc rs x y=
      preparedCurrent (readerReal k row) p left right lc ls rc rs x y+
        Complex.I*preparedCurrent (readerImag k row) p left right lc ls rc rs x y := by
  change inner ℂ (sourceLeg left lc ls x)
    (fullCurrent (readerReal k row) p (legPoint right rc rs y)+
      Complex.I • fullCurrent (readerImag k row) p (legPoint right rc rs y))=_
  rw [inner_add_right,inner_smul_right]
  rfl

theorem curvatureDensityPrepared_samefilter (k : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum)
    (left right : Bool) (lc ls rc rs : Fin 2) (x y : sourceLocalSpace) :
    Tendsto (fun F : Index=>inner ℂ (embed (sourceTestApprox F (sourceLeg left lc ls x)))
      (finiteCurrent (readerReal k row) p F (sourceLeg right rc rs y))+
      Complex.I*inner ℂ (embed (sourceTestApprox F (sourceLeg left lc ls x)))
        (finiteCurrent (readerImag k row) p F (sourceLeg right rc rs y))) sourceFilter
      (𝓝 (curvatureDensityPrepared k row p left right lc ls rc rs x y)) := by
  rw [curvatureDensityPrepared_original]
  exact (preparedCurrent_samefilter _ _ _ _ _ _ _ _ _ _).add
    ((preparedCurrent_samefilter _ _ _ _ _ _ _ _ _ _).const_mul Complex.I)

def equalTimeDensityVertex (k ell : Fin 4 → ℂ) (i j : Fin 36) (p q : PhysicalMomentum) :
    localCarrier →L[ℂ] localCarrier :=
  curvatureDensityCurrent k i p*curvatureDensityCurrent ell j q-curvatureDensityCurrent ell j q*curvatureDensityCurrent k i p

theorem equalTimeDensityVertex_norm (k ell : Fin 4 → ℂ) (i j : Fin 36) (p q : PhysicalMomentum) :
    ‖equalTimeDensityVertex k ell i j p q‖ ≤ 2*curvaturePrice k i p*curvaturePrice ell j q := by
  exact commutator_norm (curvatureDensityCurrent k i p) (curvatureDensityCurrent ell j q)
    (curvaturePrice k i p) (curvaturePrice ell j q) (curvatureDensityCurrent_norm _ _ _)
    (curvatureDensityCurrent_norm _ _ _)
    (add_nonneg (currentPrice_nonnegative _ _) (currentPrice_nonnegative _ _))
    (add_nonneg (currentPrice_nonnegative _ _) (currentPrice_nonnegative _ _))

-- These are the same original reader rows, including their unconsumed endpoint/constraint slots.
def curvatureFieldReturn (k : Fin 4 → ℂ) (row : Fin 36) (z : SourceCoordinateSlice) :
    RemainingFieldChannels × RemainingFieldChannels :=
  (remainingChannels (readerReal k row) z,remainingChannels (readerImag k row) z)

theorem curvature_primal_return (k : Fin 4 → ℂ) (z : SourceCoordinateSlice) :
    (curvatureFieldReturn k 33 z).1.primal 1 0 0=1/2 :=
  curvature_primal_retained k z

open PreparationVacuumPreparedTail PreparationVacuumTailOperator PreparationVacuumTailSupport
open SaturationMonoid.Quantum.Forms

theorem actual_full_tail_current_input (B : ℕ → Fin 5 → ℕ → ℝ)
    (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102)
    (epsilon : ℝ) (precision : 0<epsilon) :
    ∃ x : (BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense
      (completeNativeRemainder B positive input)).domain,
      ‖prepared (zeroLocalizedProfile actualNativeLocalizer x.val)‖=1 ∧
      ‖BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense
        (completeNativeRemainder B positive input) x-
        (BoundedRemainder.energy sourceClosedFactor sourceClosedFactor_closed
          (completeNativeRemainder B positive input):ℂ) • x.val‖<epsilon ∧
      (∀ (k : Fin 4 → ℂ) (row : Fin 36) (p : PhysicalMomentum)
        (left right : Bool) (lc ls rc rs : Fin 2),
        Tendsto (fun F : Index=>inner ℂ (embed (sourceTestApprox F (sourceLeg left lc ls x.val)))
          (finiteCurrent (readerReal k row) p F (sourceLeg right rc rs x.val))+
          Complex.I*inner ℂ (embed (sourceTestApprox F (sourceLeg left lc ls x.val)))
            (finiteCurrent (readerImag k row) p F (sourceLeg right rc rs x.val))) sourceFilter
          (𝓝 (curvatureDensityPrepared k row p left right lc ls rc rs x.val x.val))) := by
  obtain ⟨x,unit,near,_⟩:=actual_full_tail_preparation B positive input epsilon precision
  exact ⟨x,unit,near,fun k row p left right lc ls rc rs=>
    curvatureDensityPrepared_samefilter k row p left right lc ls rc rs x.val x.val⟩

end LowEnergy.PreparationVacuumPreparedCurrent
