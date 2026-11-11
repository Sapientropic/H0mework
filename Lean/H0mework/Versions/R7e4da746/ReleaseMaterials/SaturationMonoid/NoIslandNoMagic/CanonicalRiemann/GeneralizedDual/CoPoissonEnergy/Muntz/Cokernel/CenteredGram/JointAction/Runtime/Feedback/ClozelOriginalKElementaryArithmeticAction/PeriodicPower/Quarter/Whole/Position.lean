import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.FourierContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Position
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.FourierContact
open scoped Topology InnerProductSpace
open private sourceOneMinusSquare_reflect from
  H0mework.Versions.R7e4da746.Arithmetic.RieszForcing.SourceParity
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "F"=>fourierL2
local notation "Rq"=>burnolQuarterRestriction
local notation "Eq"=>burnolQuarterZeroExtension
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "P0"=>Constructor.zeroMean
local notation "BI"=>burnolMeanZeroBlockInverse
local notation "K"=>burnolCompletedMellinRieszVector
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The original physical reader is called on the source-generated physical projection. -/
theorem actual_original_physical_read (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (K d:BurnolL2) (wholeValue c zero h positive)=
      mellin ((burnolEvenAmbientProjection (wholeValue c zero h positive):BurnolL2):ℝ→ℂ) (1-d.value):=by
  let physical:=burnolEvenAmbientProjection (wholeValue c zero h positive)
  have native:=burnolCompletedMellinRieszVector_readback d physical
  have projected:=Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K d)
    (wholeValue c zero h positive)
  change inner ℂ (K d:BurnolL2) (physical:BurnolL2)=
    inner ℂ (K d:BurnolL2) (wholeValue c zero h positive) at projected
  change inner ℂ (K d:BurnolL2) (physical:BurnolL2)=burnolCompletedMellinEvaluator d physical at native
  have restricted:=congrArg (fun f:BurnolPaAmbientCarrier→L[ℂ]ℂ=>f physical)
    (burnolAmbientCompletedMellinEvaluator_restrict d)
  change burnolAmbientCompletedMellinEvaluator d (physical:BurnolL2)=
    burnolCompletedMellinEvaluator d physical at restricted
  rw [projected,←restricted] at native
  rw [native]
  exact AmbientMellin.evaluator_eq_mellin d (physical:BurnolL2)
    (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius physical)
    (burnolGenericPhysicalValue_gap physical).symm

private theorem whole_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):reflectL2 (wholeValue c zero h positive)=wholeValue c zero h positive:=by
  have mapped:=reflectL2.toContinuousLinearMap.hasSum (actual_value_completion c zero h positive)
  have source:HasSum (fun n:ℕ=>reflectL2 (valuePiece c zero h positive.le n))
      (wholeValue c zero h positive):=by
    apply (actual_value_completion c zero h positive).congr_fun
    intro n
    rw [valuePiece,map_smul,reflectL2_burnolMultiplicativeDilation,
      ←fourierL2_reflectL2_commute,actual_counted_even]
  exact mapped.unique source

private theorem whole_even_part (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):burnolAmbientEvenPart (wholeValue c zero h positive)=wholeValue c zero h positive:=by
  rw [burnolAmbientEvenPart,whole_even c zero h positive]
  module

private theorem projected_constant (z:ℂ):P0 (z • intervalConstant q)=0:=by
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (z • intervalConstant q)=0
  exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
    (Submodule.smul_mem _ z (Submodule.mem_span_singleton_self _))

theorem actual_whole_fourier_rhs (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):burnolAmbientMeanZeroFourier (wholeValue c zero h positive)=0:=by
  rw [burnolAmbientMeanZeroFourier,whole_even_part c zero h positive]
  change P0 (Rq (F (wholeValue c zero h positive)))=0
  rw [actual_whole_fourier_quarter,projected_constant]

def positionSource (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):M:=P0 (Rq (wholeValue c zero h positive))

def positionInverse (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):M:=BI (positionSource c zero h positive)

theorem actual_position_equation (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    burnolMeanZeroOneMinusSquare (positionInverse c zero h positive)=positionSource c zero h positive:=by
  change (burnolMeanZeroOneMinusSquare*BI) (positionSource c zero h positive)=_
  rw [burnolMeanZeroBlockInverse_right]
  rfl

theorem actual_whole_first_correction (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):burnolAmbientMeanZeroFirstCorrection (wholeValue c zero h positive)=
      positionInverse c zero h positive:=by
  rw [burnolAmbientMeanZeroFirstCorrection,burnolMeanZeroBlockFirst,burnolAmbientMeanZeroBlockRhs,
    actual_whole_fourier_rhs,map_zero,sub_zero]
  rw [burnolAmbientMeanZeroPosition,whole_even_part c zero h positive]
  rfl

theorem actual_whole_second_correction (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):burnolAmbientMeanZeroSecondCorrection (wholeValue c zero h positive)=
      -S (positionInverse c zero h positive):=by
  change burnolAmbientMeanZeroFourier (wholeValue c zero h positive)-
    S (burnolAmbientMeanZeroFirstCorrection (wholeValue c zero h positive))=_
  rw [actual_whole_fourier_rhs,actual_whole_first_correction,zero_sub]

private theorem inverse_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):reflectRestricted q (positionInverse c zero h positive:Hq)=
      (positionInverse c zero h positive:Hq):=by
  have sourceFixed:sourceMeanZeroReflection (positionSource c zero h positive)=positionSource c zero h positive:=by
    apply Subtype.ext
    have source:=burnolAmbientMeanZeroPosition_reflection_fixed (wholeValue c zero h positive)
    rw [burnolAmbientMeanZeroPosition,whole_even_part c zero h positive] at source
    exact source
  have reflected:burnolMeanZeroOneMinusSquare (sourceMeanZeroReflection (positionInverse c zero h positive))=
      positionSource c zero h positive:=by
    rw [sourceOneMinusSquare_reflect,actual_position_equation,sourceFixed]
  have recovered:=congrArg BI reflected
  change (BI*burnolMeanZeroOneMinusSquare) (sourceMeanZeroReflection (positionInverse c zero h positive))=
    positionInverse c zero h positive at recovered
  have inverseLeft:BI*burnolMeanZeroOneMinusSquare=1:=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  rw [inverseLeft] at recovered
  exact congrArg (fun x:M=>(x:Hq)) recovered

private theorem inverse_return_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):reflectRestricted q (S (positionInverse c zero h positive):Hq)=
      (S (positionInverse c zero h positive):Hq):=by
  have even:sourceMeanZeroReflection (positionInverse c zero h positive)=positionInverse c zero h positive:=
    Subtype.ext (inverse_even c zero h positive)
  have source:=sourceMeanZeroFourier_reflect (positionInverse c zero h positive)
  rw [even] at source
  exact congrArg (fun x:M=>(x:Hq)) source.symm

/-- The two original block corrections are calculated from Whole's actual position source. -/
theorem actual_whole_physical_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    (burnolEvenAmbientProjection (wholeValue c zero h positive):BurnolL2)=
      wholeValue c zero h positive-Eq (positionInverse c zero h positive:Hq)+
        F (Eq (S (positionInverse c zero h positive):Hq)):=by
  have evenRaw:reflectL2 (Eq (positionInverse c zero h positive:Hq)-
      F (Eq (S (positionInverse c zero h positive):Hq)))=
      Eq (positionInverse c zero h positive:Hq)-F (Eq (S (positionInverse c zero h positive):Hq)):=by
    rw [map_sub,show Eq=burnolRadiusZeroExtension q from rfl,burnolRadiusZeroExtension_reflect,
      inverse_even,←fourierL2_reflectL2_commute,burnolRadiusZeroExtension_reflect,inverse_return_even]
  change (((evenBurnolClosedFace q).toSubmodule.orthogonalProjectionOnto
    (wholeValue c zero h positive)):BurnolL2)=_
  rw [burnolEvenOrthogonalProjectionOnto_eq_resolventFormula,burnolAmbientExtendedSonineProjectionFormula,
    whole_even_part c zero h positive,burnolAmbientEvenMeanZeroCorrection,burnolAmbientRawMeanZeroCorrection,
    actual_whole_first_correction,actual_whole_second_correction]
  simp only [NegMemClass.coe_neg,map_neg]
  rw [show Eq (positionInverse c zero h positive:Hq)+ -F (Eq (S (positionInverse c zero h positive):Hq))=
    Eq (positionInverse c zero h positive:Hq)-F (Eq (S (positionInverse c zero h positive):Hq)) by module,
    burnolAmbientEvenPart,evenRaw]
  module

/-- The original Riesz consumer reads this full corrected field, rather than the uncorrected bulk Mellin value. -/
theorem actual_original_position_price (c d:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (positive:0<h):
    inner ℂ (K d:BurnolL2) (wholeValue c zero h positive)=
      mellin ((wholeValue c zero h positive-Eq (positionInverse c zero h positive:Hq)+
        F (Eq (S (positionInverse c zero h positive):Hq)):BurnolL2):ℝ→ℂ) (1-d.value):=by
  rw [actual_original_physical_read c d zero h positive,actual_whole_physical_source]


private theorem state_decomp (x:Hq):x=(P0 x:Hq)+burnolQuarterMeanCoefficient x • intervalConstant q:=by
  rw [Constructor.zeroMean_read]
  module

private theorem truncated_decomp (a:M):burnolTruncatedFourier (a:Hq)=
    (S a:Hq)+burnolQuarterMeanCoefficient (burnolTruncatedFourier (a:Hq)) • intervalConstant q:=by
  rw [burnolMeanZeroTruncatedFourier_coe,burnolMeanZeroProjection_eq_sub_constant]
  module

/-- The position gap keeps Whole's complete mean and the return of its actual inverse. -/
theorem actual_physical_position_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    Rq (burnolEvenAmbientProjection (wholeValue c zero h positive):BurnolL2)=
      (burnolQuarterMeanCoefficient (Rq (wholeValue c zero h positive))+
        burnolQuarterMeanCoefficient (burnolTruncatedFourier (S (positionInverse c zero h positive):Hq))) • intervalConstant q:=by
  have equation:=congrArg (fun x:M=>(x:Hq)) (actual_position_equation c zero h positive)
  change (positionInverse c zero h positive:Hq)-(S (S (positionInverse c zero h positive)):Hq)=
    (P0 (Rq (wholeValue c zero h positive)):Hq) at equation
  rw [actual_whole_physical_source,map_add,map_sub,burnolQuarterRestriction_zeroExtension]
  change Rq (wholeValue c zero h positive)-(positionInverse c zero h positive:Hq)+
    burnolTruncatedFourier (S (positionInverse c zero h positive):Hq)=_
  conv_lhs => rw [state_decomp (Rq (wholeValue c zero h positive)),truncated_decomp]
  rw [←equation]
  module

/-- The second Unit retains the original H mean and the inverse's genuine Fourier mean. -/
theorem actual_physical_fourier_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    Rq (F (burnolEvenAmbientProjection (wholeValue c zero h positive):BurnolL2))=
      (-quarterMean c/4-burnolQuarterMeanCoefficient
        (burnolTruncatedFourier (positionInverse c zero h positive:Hq))) • intervalConstant q:=by
  have returned:reflectL2 (Eq (S (positionInverse c zero h positive):Hq))=
      Eq (S (positionInverse c zero h positive):Hq):=by
    rw [show Eq=burnolRadiusZeroExtension q from rfl,burnolRadiusZeroExtension_reflect,inverse_return_even]
  rw [actual_whole_physical_source,map_add,map_sub,fourierL2_fourierL2,returned,map_add,map_sub,
    burnolQuarterRestriction_zeroExtension,actual_whole_fourier_quarter]
  change (-quarterMean c/4) • intervalConstant q-
    burnolTruncatedFourier (positionInverse c zero h positive:Hq)+(S (positionInverse c zero h positive):Hq)=_
  conv_lhs => rw [truncated_decomp]
  module

private theorem counted_memLp (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):MemLp (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting.wholeCountedRaw c) 2 volume:=
  (Lp.memLp (F (wholeValue c zero h positive))).ae_eq
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting.actual_whole_fourier_raw c zero h positive)

/-- The carrier is generated from the literal finite-count source, retaining its full Unit. -/
def countedSource (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):BurnolL2:=
  (counted_memLp c zero h positive).toLp (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting.wholeCountedRaw c)

theorem actual_counted_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):countedSource c zero h positive=F (wholeValue c zero h positive):=by
  apply Lp.ext
  exact (counted_memLp c zero h positive).coeFn_toLp.trans
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Counting.actual_whole_fourier_raw c zero h positive).symm

/-- The original inverse receives this whole count's actual Fourier field, rather than a Pa substitute. -/
theorem actual_position_counted_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):positionInverse c zero h positive=
      BI (P0 (Rq (F (countedSource c zero h positive)))):=by
  rw [actual_counted_source,fourierL2_fourierL2,whole_even]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Position
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
