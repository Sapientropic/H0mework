import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRProjectionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.OutsideQuarterAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Joint

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRContactSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalCommonInverseForcing.SourceJoint
open OriginalKPairedBEulerJunctionSource
open scoped InnerProductSpace Topology

local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "F" => fourierL2
local notation "P" => burnolEvenAmbientProjection
local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Eq" => burnolQuarterZeroExtension
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "h0" => junctionShift
local notation "u" => upperSeedFactor h0
local notation "PD" => OriginalWholeDebtRProjectionSource.projectedDebt
local notation "Z" => OriginalWholeDebtRProjectionSource.kernelRBoundary
local notation "alpha" => OriginalWholeDebtRProjectionSource.powerReturnPrice
local notation "beta" => OriginalWholeDebtRProjectionSource.fourierDebtPrice
local notation "field" => OriginalWholeDebtRProjectionSource.sourceField

open private weighted_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource

private def face (i : Fin 2) (value : BurnolL2) : BurnolL2 := ![value,F value] i

private def physicalRaw (value : BurnolPaAmbientCarrier) : ℝ → ℂ :=
  burnolEvenProjectionRaw value value

private theorem physical_raw_read (value : BurnolPaAmbientCarrier) :
    (value : ℝ → ℂ)=ᵐ[volume] physicalRaw value := by
  have paid := burnolEvenProjection_ae_raw (value : BurnolL2) value EventuallyEq.rfl
  have fixed : P (value : BurnolL2)=value :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  change ((P (value : BurnolL2) : BurnolL2) : ℝ → ℂ)=ᵐ[volume] _ at paid
  simpa only [fixed,physicalRaw] using paid

private theorem physical_raw_gap (value : BurnolPaAmbientCarrier) :
    ∀ {x : ℝ}, |x|≤q → physicalRaw value x=physicalRaw value 0 := by
  intro x inside
  rw [physicalRaw,burnolEvenProjectionRaw_gap_read _ _ (abs_le.mp inside),
    burnolEvenProjectionRaw_gap_read _ _ (by norm_num [symmetricInterval])]

private theorem prefix_continuous (c : BurnolCompletedMellinCoordinate) (raw : ℝ → ℂ)
    (native : MemLp raw 2 volume) (gap : ∀ {x : ℝ}, |x|≤q → raw x=raw 0)
    {x : ℝ} (nz : x≠0) :
    ContinuousAt (OriginalKCenteredMobiusRSource.sourceRRaw c raw) x := by
  have xp : 0 < |x| := abs_pos.mpr nz
  have paid := weighted_integrable c raw native gap (|x|+1) (by linarith)
  have primitive : ContinuousOn
      (fun t : ℝ => ∫ v : ℝ in 0..t,OriginalKCenteredMobiusRSource.weightedCentered c raw v)
      (Icc 0 (|x|+1)) := by
    simpa only [uIcc_of_le (by linarith : (0 : ℝ) ≤ |x|+1)] using
      intervalIntegral.continuousOn_primitive_interval' paid left_mem_uIcc
  have atPoint : ContinuousAt
      (fun t : ℝ => ∫ v : ℝ in 0..t,OriginalKCenteredMobiusRSource.weightedCentered c raw v) |x| :=
    primitive.continuousAt (Icc_mem_nhds xp (by linarith))
  have moved := atPoint.comp continuous_abs.continuousAt
  have power := (Complex.continuousAt_ofReal_cpow_const |x| (-c.value)
    (Or.inr xp.ne')).comp continuous_abs.continuousAt
  unfold OriginalKCenteredMobiusRSource.sourceRRaw
  exact continuousAt_const.sub ((continuousAt_const.mul power).mul moved)

private def outwardRaw (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (x : ℝ) : ℂ :=
  -2*((|x| : ℝ) : ℂ)^(c.value-1)*
    (∫ t : ℝ in Ioi |x|,(t : ℂ)^(-c.value)*value t)

private theorem tail_continuous (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    {x : ℝ} (positive : 0<x) :
    ContinuousAt (fun y : ℝ => ∫ t : ℝ in Ioi y,(t : ℂ)^(-c.value)*value t) x := by
  let f : ℝ → ℂ := fun t => (t : ℂ)^(-c.value)*value t
  have paid : IntegrableOn f (Ioi (x/2)) :=
    burnolRadiusMellinWeight_integrableOn_tail (x/2) (by linarith) c.value c.rightHalf value
  have localInt : IntervalIntegrable f volume (x/2) (x+1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
      (paid.mono_set Ioc_subset_Ioi_self)
  have continuous : ContinuousOn (fun y : ℝ => ∫ t : ℝ in (x/2)..y,f t)
      (Icc (x/2) (x+1)) := by
    simpa only [uIcc_of_le (by linarith : x/2≤x+1)] using
      intervalIntegral.continuousOn_primitive_interval' localInt left_mem_uIcc
  have atPoint : ContinuousAt (fun y : ℝ => ∫ t : ℝ in (x/2)..y,f t) x :=
    continuous.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have companion : ContinuousAt
      (fun y : ℝ => (∫ t : ℝ in Ioi (x/2),f t)-(∫ t : ℝ in (x/2)..y,f t)) x :=
    continuousAt_const.sub atPoint
  apply companion.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (by linarith : x/2<x)] with y hy
  have actual := intervalIntegral.integral_Ioi_sub_Ioi paid hy.le
  dsimp only [f] at actual ⊢
  linear_combination -actual

private theorem outward_continuous (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    {x : ℝ} (nz : x≠0) : ContinuousAt (outwardRaw c value) x := by
  have xp := abs_pos.mpr nz
  have tail := (tail_continuous c value xp).comp continuous_abs.continuousAt
  have power := (Complex.continuousAt_ofReal_cpow_const |x| (c.value-1)
    (Or.inr xp.ne')).comp continuous_abs.continuousAt
  exact (continuousAt_const.mul power).mul tail

private theorem even_read (value : BurnolL2) (raw : ℝ → ℂ)
    (even : reflectL2 value=value) (rawEven : ∀ x,raw (-x)=raw x)
    (positive : ∀ᵐ x : ℝ ∂volume,0<x → value x=raw x) :
    (value : ℝ → ℂ)=ᵐ[volume] raw := by
  have reflected := Lp.coeFn_compMeasurePreserving value negMeasurePreserving
  change (reflectL2 value : ℝ → ℂ)=ᵐ[volume] fun x => value (-x) at reflected
  rw [even] at reflected
  filter_upwards [positive,negMeasurePreserving.quasiMeasurePreserving.ae positive,
    reflected,volume.ae_ne (0 : ℝ)] with x direct reverse parity nz
  by_cases pos : 0<x
  · exact direct pos
  · have neg : x<0 := lt_of_le_of_ne (le_of_not_gt pos) nz
    rw [parity,reverse (by linarith),rawEven]

private def rRaw (c : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier)
    (raw : ℝ → ℂ) (i : Fin 2) : ℝ → ℂ :=
  ![OriginalKCenteredMobiusRSource.sourceRRaw c raw,outwardRaw c (F value)] i

private theorem r_read (c : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier)
    (raw : ℝ → ℂ) (read : (value : ℝ → ℂ)=ᵐ[volume] raw)
    (gap : ∀ {x : ℝ},|x|≤q → raw x=raw 0) (i : Fin 2) :
    (face i (R c (value : BurnolL2)) : ℝ → ℂ)=ᵐ[volume] rRaw c value raw i := by
  have even := mem_evenL2ClosedFace_iff.mp value.property.2
  fin_cases i
  · exact OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_R_even_read c value raw read gap even
  · have actedEven := OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_iterate_even
      c (value : BurnolL2) even 1
    change reflectL2 (R c (value : BurnolL2))=R c (value : BurnolL2) at actedEven
    apply even_read (F (R c (value : BurnolL2))) (outwardRaw c (F value))
      (by rw [←fourierL2_reflectL2_commute,actedEven])
      (by intro x; simp only [outwardRaw,abs_neg])
    have actual := sourceVolterraResolvent_positive_profile c (F value)
    have identity : sourceVolterraResolvent c (F (value : BurnolL2))=F (R c (value : BurnolL2)) :=
      OriginalKDirectRCofinalOutsideVolterraSource.source_fourier_input c value
    rw [identity] at actual
    filter_upwards [actual] with x profile positive
    simpa only [outwardRaw,abs_of_pos positive,burnolRadiusMellinTailEvaluator_eq_integral] using profile positive

private theorem r_continuous (c : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier)
    (raw : ℝ → ℂ) (read : (value : ℝ → ℂ)=ᵐ[volume] raw)
    (gap : ∀ {x : ℝ},|x|≤q → raw x=raw 0) (i : Fin 2)
    {x : ℝ} (nz : x≠0) : ContinuousAt (rRaw c value raw i) x := by
  fin_cases i
  · exact prefix_continuous c raw ((memLp_congr_ae read).mp (Lp.memLp _)) gap nz
  · exact outward_continuous c (F value) nz

private theorem kernel_gap (c : BurnolCompletedMellinCoordinate) :
    ∀ {x : ℝ},|x|≤q → burnolRieszStateRaw c x=burnolRieszStateRaw c 0 := by
  intro x inside
  rw [burnolRieszStateRaw_eq_quarterInner_of_mem c (abs_le.mp inside),
    burnolRieszStateRaw_eq_quarterInner_of_mem c (by norm_num [symmetricInterval])]

private def kernelRRaw (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : ℝ → ℂ :=
  rRaw c (K c) (burnolRieszStateRaw c) i

private def pairedRaw (raw : ℝ → ℂ) (shift x : ℝ) : ℂ :=
  (1/2 : ℂ)*((Real.exp (shift/2) : ℂ)*raw (Real.exp shift*x)+
    (Real.exp (-shift/2) : ℂ)*raw (Real.exp (-shift)*x))

private theorem paired_read (value : BurnolL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ)=ᵐ[volume] raw) (shift : ℝ) :
    (pairedBurnolMultiplicativeDilation shift value : ℝ → ℂ)=ᵐ[volume] pairedRaw raw shift := by
  have scaled (s : ℝ) : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp s*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := Real.exp s) (Real.exp_ne_zero s)
  filter_upwards [Lp.coeFn_smul (1/2 : ℂ)
      (burnolMultiplicativeDilation shift value+burnolMultiplicativeDilation (-shift) value),
    Lp.coeFn_add (burnolMultiplicativeDilation shift value) (burnolMultiplicativeDilation (-shift) value),
    burnolMultiplicativeDilation_coeFn shift value,burnolMultiplicativeDilation_coeFn (-shift) value,
    (scaled shift).ae read,(scaled (-shift)).ae read] with x hs ha hf hb rf rb
  change ((1/2 : ℂ) • (burnolMultiplicativeDilation shift value+
    burnolMultiplicativeDilation (-shift) value) : BurnolL2) x=_
  simp only [hs,ha,Pi.smul_apply,smul_eq_mul,Pi.add_apply,hf,hb,rf,rb,
    burnolL2RawNormalizedDilation,pairedRaw,neg_div]

def boundaryRaw (c : BurnolCompletedMellinCoordinate) (i : Fin 2) (x : ℝ) : ℂ :=
  pairedRaw (kernelRRaw c i) h0 x-
    pairedMellinTranslationCharacter (star c.value) h0*kernelRRaw c i x

private theorem boundary_read (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (face i (Z c) : ℝ → ℂ)=ᵐ[volume] boundaryRaw c i := by
  have native := r_read c (K c) (burnolRieszStateRaw c) (burnolRieszState_ae_raw c) (kernel_gap c) i
  have actual : face i (Z c)=pairedBurnolMultiplicativeDilation h0
      (face i (R c (K c : BurnolL2)))-
      pairedMellinTranslationCharacter (star c.value) h0 • face i (R c (K c : BurnolL2)) := by
    fin_cases i
    · rfl
    · change F (Z c)=pairedBurnolMultiplicativeDilation h0 (F (R c (K c : BurnolL2)))-
        pairedMellinTranslationCharacter (star c.value) h0 • F (R c (K c : BurnolL2))
      simp only [OriginalWholeDebtRProjectionSource.kernelRBoundary,
        map_sub,map_smul,←pairedBurnolMultiplicativeDilation_fourier]
  rw [actual]
  filter_upwards [Lp.coeFn_sub
      (pairedBurnolMultiplicativeDilation h0 (face i (R c (K c : BurnolL2))))
      (pairedMellinTranslationCharacter (star c.value) h0 • face i (R c (K c : BurnolL2))),
    Lp.coeFn_smul (pairedMellinTranslationCharacter (star c.value) h0)
      (face i (R c (K c : BurnolL2))),paired_read _ _ native h0,native]
    with x subRead scalar paired source
  simp only [subRead,scalar,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,paired,source,boundaryRaw,kernelRRaw]

private theorem boundary_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    {x : ℝ} (nz : x≠0) : ContinuousAt (boundaryRaw c i) x := by
  have k (y : ℝ) (hy : y≠0) : ContinuousAt (kernelRRaw c i) y :=
    r_continuous c (K c) (burnolRieszStateRaw c) (burnolRieszState_ae_raw c) (kernel_gap c) i hy
  have direct := (k (Real.exp h0*x) (mul_ne_zero (Real.exp_ne_zero _) nz)).comp
    (continuous_const.mul continuous_id).continuousAt
  have reverse := (k (Real.exp (-h0)*x) (mul_ne_zero (Real.exp_ne_zero _) nz)).comp
    (continuous_const.mul continuous_id).continuousAt
  unfold boundaryRaw pairedRaw
  exact ((continuousAt_const.mul ((continuousAt_const.mul direct).add
    (continuousAt_const.mul reverse))).sub (continuousAt_const.mul (k x nz)))

def boundaryTrace (c : BurnolCompletedMellinCoordinate) (i : Fin 2) : ℂ :=
  burnolEvenFirstCorrectionQuarterTrace (face i (Z c)) (boundaryRaw c i)

private def kernelRaw (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![burnolRieszStateRaw c,burnolRieszFourierRaw c]
private def kernelOuter (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![burnolRieszStatePositiveOuterRaw c,burnolRieszFourierExteriorRaw c]
private def kernelInner (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℂ :=
  ![burnolRieszStateQuarterInnerRaw c,burnolRieszFourierRaw c q]

private theorem kernel_read (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (face i (K c : BurnolL2) : ℝ → ℂ)=ᵐ[volume] kernelRaw c i := by
  fin_cases i
  · exact burnolRieszState_ae_raw c
  · exact burnolRieszFourier_ae_raw c

private theorem kernel_inner (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    {x : ℝ} (positive : 0<x) (small : x≤q) : kernelRaw c i x=kernelInner c i := by
  have inside : x∈symmetricInterval q := ⟨by linarith,small⟩
  fin_cases i
  · exact burnolRieszStateRaw_eq_quarterInner_of_mem c inside
  · change burnolRieszFourierRaw c x=burnolRieszFourierRaw c q
    rw [burnolRieszFourierRaw_gap_read c inside,
      burnolRieszFourierRaw_gap_read c (by norm_num [symmetricInterval])]

private theorem kernel_outer (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    {x : ℝ} (outside : q<x) : kernelRaw c i x=kernelOuter c i x := by
  fin_cases i
  · exact burnolRieszStateRaw_eq_positiveOuter c outside
  · change burnolRieszFourierRaw c x=burnolRieszFourierExteriorRaw c x
    unfold burnolRieszFourierRaw burnolEvenRaw
    have a : x∉symmetricInterval q := by intro inside;exact (not_le_of_gt outside) inside.2
    have b : -x∉symmetricInterval q := by intro inside;linarith [inside.1]
    rw [indicator_of_notMem a,indicator_of_notMem b]
    ring

private theorem kernel_outer_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    {x : ℝ} (positive : 0<x) : ContinuousAt (kernelOuter c i) x := by
  fin_cases i
  · change ContinuousAt (burnolRieszStatePositiveOuterRaw c) x
    have power := Complex.continuousAt_ofReal_cpow_const x (-star c.value) (Or.inr positive.ne')
    have trunc := burnolRadiusTruncatedFourierRaw_continuous
      (burnolRieszSingleFourierSource c : Hq)
    unfold burnolRieszStatePositiveOuterRaw
    exact (continuousAt_const.mul power).sub
      (continuousAt_const.mul (trunc.continuousAt.add (trunc.continuousAt.comp continuousAt_neg)))
  · change ContinuousAt (burnolRieszFourierExteriorRaw c) x
    exact burnolRieszFourierExteriorRaw_continuousAt c positive.ne'

private theorem kernel_jump (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    kernelOuter c i q-kernelInner c i= ![-Kernel.A c,Kernel.beta c] i := by
  fin_cases i
  · exact Kernel.position_jump c
  · change burnolRieszFourierExteriorRaw c q-burnolRieszFourierRaw c q=Kernel.beta c
    rw [burnolRieszFourierRaw_gap_read c (frequency := q) (by norm_num [symmetricInterval])]
    exact Kernel.fourier_jump c

private def H (c : BurnolCompletedMellinCoordinate) : M := hPowerBColumn (barC c)
private def hRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ := logFirstRaw (barC c) 0
private def sRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ := burnolMeanZeroFourierRaw (H c)
def returnTrace (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℂ := ![sRaw c q,hRaw c q]

private def vInner (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![fun x => burnolRadiusTruncatedFourierRaw q (H c : Hq) x-sRaw c x,
    fun x => hRaw c x-burnolRadiusTruncatedFourierRaw q (S (H c) : Hq) x]
private def vOuter (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![burnolRadiusTruncatedFourierRaw q (H c : Hq),
    fun x => -burnolRadiusTruncatedFourierRaw q (S (H c) : Hq) x]
private def vRaw (c : BurnolCompletedMellinCoordinate) : Fin 2 → ℝ → ℂ :=
  ![fun x => burnolRadiusTruncatedFourierRaw q (H c : Hq) x-
      (symmetricInterval q).indicator (sRaw c) x,
    fun x => (symmetricInterval q).indicator (hRaw c) x-
      burnolRadiusTruncatedFourierRaw q (S (H c) : Hq) x]

private theorem extension_read (v : M) (raw : ℝ → ℂ)
    (read : (v : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] raw) :
    (Eq (v : Hq) : ℝ → ℂ)=ᵐ[volume] (symmetricInterval q).indicator raw := by
  have paid := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp read
  filter_upwards [burnolRadiusZeroExtension_coe (v : Hq),paid] with x extended source
  change (burnolRadiusZeroExtension q (v : Hq) : ℝ → ℂ) x=_
  rw [extended]
  by_cases inside : x∈symmetricInterval q
  · simp only [indicator_of_mem inside,source inside]
  · simp only [indicator_of_notMem inside]

private theorem v_read (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    (face i (physicalOutsideColumn c) : ℝ → ℂ)=ᵐ[volume] vRaw c i := by
  have hread : (H c : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] hRaw c :=
    log_first_profile (barC c) 0
  have sread : (S (H c) : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)] sRaw c :=
    burnolMeanZeroFourier_ae_raw (H c)
  have evenH : reflectL2 (Eq (H c : Hq))=Eq (H c : Hq) := by
    change reflectL2 (burnolRadiusZeroExtension q (H c : Hq))=_
    rw [burnolRadiusZeroExtension_reflect]
    exact congrArg Eq (congrArg (fun v : M => (v : Hq)) (log_B_even (barC c) 0))
  have source := OriginalKFiniteOrderRelease.OutsideQuarterAction.physicalOutsideColumn_embedding c
  rw [source,OriginalKFiniteOrderRelease.OutsideQuarterAction.outsideEmbedding_read]
  fin_cases i
  · change ((F (Eq (H c : Hq))-Eq (S (H c) : Hq) : BurnolL2) : ℝ → ℂ)=ᵐ[volume]
      fun x => burnolRadiusTruncatedFourierRaw q (H c : Hq) x-(symmetricInterval q).indicator (sRaw c) x
    filter_upwards [Lp.coeFn_sub (F (Eq (H c : Hq))) (Eq (S (H c) : Hq)),
      burnolRadiusFourierL2_zeroExtension_ae_eq_raw (H c : Hq),extension_read (S (H c)) _ sread]
      with x subRead first second
    change (F (Eq (H c : Hq))) x=_ at first
    rw [subRead]
    change (F (Eq (H c : Hq))) x-(Eq (S (H c) : Hq)) x=_
    rw [first,second]
  · change ((F (F (Eq (H c : Hq))-Eq (S (H c) : Hq)) : BurnolL2) : ℝ → ℂ)=ᵐ[volume] _
    rw [map_sub,fourierL2_fourierL2,evenH]
    change ((Eq (H c : Hq)-F (Eq (S (H c) : Hq)) : BurnolL2) : ℝ → ℂ)=ᵐ[volume]
      fun x => (symmetricInterval q).indicator (hRaw c) x-burnolRadiusTruncatedFourierRaw q (S (H c) : Hq) x
    filter_upwards [Lp.coeFn_sub (Eq (H c : Hq)) (F (Eq (S (H c) : Hq))),
      extension_read (H c) _ hread,burnolRadiusFourierL2_zeroExtension_ae_eq_raw (S (H c) : Hq)]
      with x subRead first second
    change (F (Eq (S (H c) : Hq))) x=_ at second
    rw [subRead]
    change (Eq (H c : Hq)) x-(F (Eq (S (H c) : Hq))) x=_
    rw [first,second]

private theorem v_piece (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    {x : ℝ} (positive : 0<x) :
    (x≤q → vRaw c i x=vInner c i x) ∧ (q<x → vRaw c i x=vOuter c i x) := by
  constructor
  · intro small
    have inside : x∈symmetricInterval q := ⟨by linarith,small⟩
    fin_cases i
    · change burnolRadiusTruncatedFourierRaw q (H c : Hq) x-(symmetricInterval q).indicator (sRaw c) x=_
      rw [indicator_of_mem inside]
      rfl
    · change (symmetricInterval q).indicator (hRaw c) x-burnolRadiusTruncatedFourierRaw q (S (H c) : Hq) x=_
      rw [indicator_of_mem inside]
      rfl
  · intro large
    have outside : x∉symmetricInterval q := by intro inside;exact (not_le_of_gt large) inside.2
    fin_cases i
    · change burnolRadiusTruncatedFourierRaw q (H c : Hq) x-(symmetricInterval q).indicator (sRaw c) x=_
      rw [indicator_of_notMem outside,sub_zero]
      rfl
    · change (symmetricInterval q).indicator (hRaw c) x-burnolRadiusTruncatedFourierRaw q (S (H c) : Hq) x=_
      rw [indicator_of_notMem outside,zero_sub]
      rfl

private theorem v_piece_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    {x : ℝ} (positive : 0<x) :
    ContinuousAt (vInner c i) x ∧ ContinuousAt (vOuter c i) x := by
  have trunc (v : Hq) := (burnolRadiusTruncatedFourierRaw_continuous v).continuousAt (x := x)
  have meanFourier (v : M) : Continuous (burnolMeanZeroFourierRaw v) :=
    (burnolRadiusTruncatedFourierRaw_continuous (v : Hq)).sub continuous_const
  have scont : ContinuousAt (sRaw c) x := (meanFourier (H c)).continuousAt
  have power : ContinuousAt (SingularCounting.powerRaw (barC c)) x :=
    (Complex.continuousAt_ofReal_cpow_const |x| (star (barC c).value-1)
      (Or.inr (abs_pos.mpr positive.ne').ne')).comp continuous_abs.continuousAt
  have hcont : ContinuousAt (hRaw c) x := by
    unfold hRaw logFirstRaw
    simp only [dividedLogRaw,pow_zero,Nat.factorial_zero,Nat.cast_one,
      mul_one,div_one,InverseAction.centeredRaw]
    exact (power.sub continuousAt_const).add
      (meanFourier (S (logBFirst (barC c) 0))).continuousAt
  fin_cases i
  · constructor
    · exact (trunc (H c : Hq)).sub scont
    · exact trunc (H c : Hq)
  · constructor
    · exact hcont.sub (trunc (S (H c) : Hq))
    · exact (trunc (S (H c) : Hq)).neg

private theorem v_jump (c : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    vOuter c i q-vInner c i q=![returnTrace c 0,-returnTrace c 1] i := by
  fin_cases i
  · change burnolRadiusTruncatedFourierRaw q (H c : Hq) q-
      (burnolRadiusTruncatedFourierRaw q (H c : Hq) q-sRaw c q)=sRaw c q
    ring
  · change -burnolRadiusTruncatedFourierRaw q (S (H c) : Hq) q-
      (hRaw c q-burnolRadiusTruncatedFourierRaw q (S (H c) : Hq) q)= -hRaw c q
    ring

private theorem projection_continuous (c : BurnolCompletedMellinCoordinate) (i : Fin 2)
    {x : ℝ} (positive : 0<x) :
    ContinuousAt (burnolEvenProjectionPositiveOuterRaw (face i (Z c)) (boundaryRaw c i)) x := by
  have direct := boundary_continuous c i positive.ne'
  have reflected := (boundary_continuous c i (neg_ne_zero.mpr positive.ne')).comp continuousAt_neg
  have trunc := burnolRadiusTruncatedFourierRaw_continuous
    (burnolAmbientMeanZeroSecondCorrection (face i (Z c)) : Hq)
  unfold burnolEvenProjectionPositiveOuterRaw burnolEvenRaw
  exact (continuousAt_const.mul (direct.add reflected)).sub
    (continuousAt_const.mul (trunc.continuousAt.add (trunc.continuousAt.comp continuousAt_neg)))

private theorem raw_combination (v0 v1 v2 v3 : BurnolL2) (r0 r1 r2 r3 : ℝ → ℂ)
    (a b d : ℂ) (source0 : (v0 : ℝ → ℂ)=ᵐ[volume] r0)
    (source1 : (v1 : ℝ → ℂ)=ᵐ[volume] r1) (source2 : (v2 : ℝ → ℂ)=ᵐ[volume] r2)
    (source3 : (v3 : ℝ → ℂ)=ᵐ[volume] r3) :
    ((v0-a • v1-b • v2-d • v3 : BurnolL2) : ℝ → ℂ)=ᵐ[volume]
      fun x => r0 x-a*r1 x-b*r2 x-d*r3 x := by
  filter_upwards [Lp.coeFn_sub (v0-a • v1-b • v2) (d • v3),
    Lp.coeFn_sub (v0-a • v1) (b • v2),Lp.coeFn_sub v0 (a • v1),
    Lp.coeFn_smul a v1,Lp.coeFn_smul b v2,Lp.coeFn_smul d v3,source0,source1,source2,source3]
    with x s0 s1 s2 m0 m1 m2 t0 t1 t2 t3
  simp only [s0,s1,s2,Pi.sub_apply,m0,m1,m2,Pi.smul_apply,smul_eq_mul,t0,t1,t2,t3]

private theorem continuous_junction {f raw inside outside : ℝ → ℂ}
    (read : f=ᵐ[volume] raw)
    (left : ∀ x,0<x → x<q → raw x=inside x)
    (right : ∀ x,q<x → raw x=outside x)
    (fc : ContinuousOn f (Ioi 0)) (ic : ContinuousOn inside (Ioi 0))
    (oc : ContinuousOn outside (Ioi 0)) : outside q-inside q=0 := by
  have leftRead : f=ᵐ[volume.restrict (Icc (q/2) q)] inside := by
    filter_upwards [ae_restrict_of_ae read,ae_restrict_of_ae (volume.ae_ne q),
      ae_restrict_mem measurableSet_Icc] with x source nz hx
    exact source.trans (left x (by linarith [hx.1]) (lt_of_le_of_ne hx.2 nz))
  have rightRead : f=ᵐ[volume.restrict (Icc q (q+1))] outside := by
    filter_upwards [ae_restrict_of_ae read,ae_restrict_of_ae (volume.ae_ne q),
      ae_restrict_mem measurableSet_Icc] with x source nz hx
    exact source.trans (right x (lt_of_le_of_ne hx.1 nz.symm))
  have leq := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : q/2≠q) leftRead
    (fc.mono (by intro x hx; change 0<x;linarith [hx.1]))
    (ic.mono (by intro x hx; change 0<x;linarith [hx.1]))
  have req := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : q≠q+1) rightRead
    (fc.mono (by intro x hx; change 0<x;linarith [hx.1]))
    (oc.mono (by intro x hx; change 0<x;linarith [hx.1]))
  rw [←leq (x := q) (by norm_num),←req (x := q) (by norm_num),sub_self]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

private def wave : BurnolPaAmbientCarrier := upperSourceWaveAmbient c h0
  junctionShift_pos.le ((le_abs_self h0).trans OriginalRieszFiniteColumns.fixedShift_small)

private def fieldRaw (i : Fin 2) (x : ℝ) : ℂ :=
  rRaw c (wave observation nontrivial half) (physicalRaw (wave observation nontrivial half)) i x-
    (2*u)*burnolEvenProjectionRaw (face i (Z c)) (boundaryRaw c i) x-
    (4*u*alpha c)*kernelRaw (barC c) i x-(2*beta c)*vRaw c i x

private def fieldInner (i : Fin 2) (x : ℝ) : ℂ :=
  rRaw c (wave observation nontrivial half) (physicalRaw (wave observation nontrivial half)) i x-
    (2*u)*burnolProjectionGapRaw (face i (Z c))-
    (4*u*alpha c)*kernelInner (barC c) i-(2*beta c)*vInner c i x

private def fieldOuter (i : Fin 2) (x : ℝ) : ℂ :=
  rRaw c (wave observation nontrivial half) (physicalRaw (wave observation nontrivial half)) i x-
    (2*u)*burnolEvenProjectionPositiveOuterRaw (face i (Z c)) (boundaryRaw c i) x-
    (4*u*alpha c)*kernelOuter (barC c) i x-(2*beta c)*vOuter c i x

private theorem original_field_read (i : Fin 2) :
    rRaw c (PD c) (physicalRaw (PD c)) i=ᵐ[volume] fieldRaw observation nontrivial half i := by
  have source := congrArg (face i) (OriginalWholeDebtRProjectionSource.original_source_action
    observation nontrivial half)
  have actual : face i (R c (PD c : BurnolL2))=
      face i (R c (wave observation nontrivial half : BurnolL2))-
      (2*u) • (P (face i (Z c)) : BurnolL2)-
      (4*u*alpha c) • face i (K (barC c) : BurnolL2)-
      (2*beta c) • face i (physicalOutsideColumn c) := by
    rw [source]
    fin_cases i
    · change field c=R c (wave observation nontrivial half : BurnolL2)-
        (2*u) • (P (Z c) : BurnolL2)-(4*u*alpha c) • (K (barC c) : BurnolL2)-
        (2*beta c) • physicalOutsideColumn c
      unfold OriginalWholeDebtRProjectionSource.sourceField
      rw [OriginalKSourceResolventReconstruction.generatedK_eq_original]
      rfl
    · change F (field c)=F (R c (wave observation nontrivial half : BurnolL2))-
        (2*u) • (P (F (Z c)) : BurnolL2)-(4*u*alpha c) • F (K (barC c) : BurnolL2)-
        (2*beta c) • F (physicalOutsideColumn c)
      unfold OriginalWholeDebtRProjectionSource.sourceField
      rw [OriginalKSourceResolventReconstruction.generatedK_eq_original]
      have commutes : F (P (Z c) : BurnolL2)=(P (F (Z c)) : BurnolL2) :=
        fourierL2_evenBurnolPhysicalProjection q (Z c)
      simp only [map_sub,map_smul]
      rw [commutes]
      rfl
  have projected := burnolEvenProjection_ae_raw (face i (Z c)) (boundaryRaw c i) (boundary_read c i)
  have combined := raw_combination
    (face i (R c (wave observation nontrivial half : BurnolL2))) (P (face i (Z c)))
    (face i (K (barC c) : BurnolL2)) (face i (physicalOutsideColumn c)) _ _ _ _
    (2*u) (4*u*alpha c) (2*beta c)
    (r_read c _ _ (physical_raw_read _) (physical_raw_gap _) i) projected
    (kernel_read (barC c) i) (v_read c i)
  exact (r_read c _ _ (physical_raw_read _) (physical_raw_gap _) i).symm.trans
    (by rw [actual];exact combined)

/-- Both q contacts are generated by the same actual R field and its native Fourier face. -/
theorem original_contact_source (i : Fin 2) :
    ![u*boundaryTrace c 0-2*u*alpha c*Kernel.A (barC c)+beta c*returnTrace c 0,
      u*boundaryTrace c 1+2*u*alpha c*Kernel.beta (barC c)-beta c*returnTrace c 1] i=0 := by
  have native := original_field_read observation nontrivial half i
  have limits := continuous_junction
    (inside := fieldInner observation nontrivial half i)
    (outside := fieldOuter observation nontrivial half i) native
    (fun x positive small => by
      unfold fieldRaw fieldInner
      rw [burnolEvenProjectionRaw_gap_read _ _ (show x∈symmetricInterval q from ⟨by linarith,small.le⟩),
        kernel_inner (barC c) i positive small.le,(v_piece c i positive).1 small.le])
    (fun x large => by
      unfold fieldRaw fieldOuter
      rw [burnolEvenProjectionRaw_eq_positiveOuter _ _ large,
        kernel_outer (barC c) i large,(v_piece c i (by linarith)).2 large])
    (fun x positive => (r_continuous c _ _ (physical_raw_read _) (physical_raw_gap _) i positive.ne').continuousWithinAt)
    (fun x positive => by
      have rc := r_continuous c (wave observation nontrivial half) _
        (physical_raw_read _) (physical_raw_gap _) i positive.ne'
      have vc := (v_piece_continuous c i positive).1
      unfold fieldInner
      exact ((rc.sub continuousAt_const).sub continuousAt_const |>.sub (continuousAt_const.mul vc)).continuousWithinAt)
    (fun x positive => by
      have rc := r_continuous c (wave observation nontrivial half) _
        (physical_raw_read _) (physical_raw_gap _) i positive.ne'
      have pc := projection_continuous c i positive
      have kc := kernel_outer_continuous (barC c) i positive
      have vc := (v_piece_continuous c i positive).2
      unfold fieldOuter
      exact (((rc.sub (continuousAt_const.mul pc)).sub (continuousAt_const.mul kc)).sub
        (continuousAt_const.mul vc)).continuousWithinAt)
  have projection : burnolEvenProjectionPositiveOuterRaw (face i (Z c)) (boundaryRaw c i) q-
      burnolProjectionGapRaw (face i (Z c))=boundaryTrace c i := by
    rw [←burnolEvenProjectionRaw_gap_read (face i (Z c)) (boundaryRaw c i)
      (x := q) (by norm_num [symmetricInterval])]
    exact burnolEvenProjectionQuarterOuterRaw_sub_projectionRaw _ _
  unfold fieldOuter fieldInner at limits
  have kernel := kernel_jump (barC c) i
  have returned := v_jump c i
  fin_cases i
  · change u*boundaryTrace c 0-2*u*alpha c*Kernel.A (barC c)+beta c*returnTrace c 0=0
    simp only [Fin.mk_zero] at limits projection
    change kernelOuter (barC c) 0 q-kernelInner (barC c) 0= -Kernel.A (barC c) at kernel
    change vOuter c 0 q-vInner c 0 q=returnTrace c 0 at returned
    linear_combination -(1/2 : ℂ)*limits-u*projection-(2*u*alpha c)*kernel-beta c*returned
  · change u*boundaryTrace c 1+2*u*alpha c*Kernel.beta (barC c)-beta c*returnTrace c 1=0
    simp only [Fin.mk_one] at limits projection
    change kernelOuter (barC c) 1 q-kernelInner (barC c) 1=Kernel.beta (barC c) at kernel
    change vOuter c 1 q-vInner c 1 q= -returnTrace c 1 at returned
    linear_combination -(1/2 : ℂ)*limits-u*projection-(2*u*alpha c)*kernel-beta c*returned

def contactDeterminant (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  Kernel.A (barC coordinate)*returnTrace coordinate 1-
    Kernel.beta (barC coordinate)*returnTrace coordinate 0

/-- Adjugate settlement keeps the determinant as generated source data; no inverse is assumed. -/
theorem original_return_settlement :
    2*u*alpha c*contactDeterminant c=
      u*(returnTrace c 1*boundaryTrace c 0+returnTrace c 0*boundaryTrace c 1) ∧
    beta c*contactDeterminant c=
      u*(Kernel.beta (barC c)*boundaryTrace c 0+Kernel.A (barC c)*boundaryTrace c 1) := by
  have first := original_contact_source observation nontrivial half 0
  have second := original_contact_source observation nontrivial half 1
  change u*boundaryTrace c 0-2*u*alpha c*Kernel.A (barC c)+beta c*returnTrace c 0=0 at first
  change u*boundaryTrace c 1+2*u*alpha c*Kernel.beta (barC c)-beta c*returnTrace c 1=0 at second
  unfold contactDeterminant
  constructor
  · linear_combination -returnTrace c 1*first-returnTrace c 0*second
  · linear_combination -Kernel.beta (barC c)*first-Kernel.A (barC c)*second

def settledField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  contactDeterminant coordinate • R coordinate (upperSourceWave coordinate h0)-
    (2*u*contactDeterminant coordinate) • (P (Z coordinate) : BurnolL2)-
    (2*u*(returnTrace coordinate 1*boundaryTrace coordinate 0+
      returnTrace coordinate 0*boundaryTrace coordinate 1)) •
        OriginalKSourceResolventReconstruction.generatedK (barC coordinate)-
    (2*u*(Kernel.beta (barC coordinate)*boundaryTrace coordinate 0+
      Kernel.A (barC coordinate)*boundaryTrace coordinate 1)) • physicalOutsideColumn coordinate

/-- Actual endpoint source replaces both complete return charges in the same R action. -/
theorem original_settled_source_action :
    contactDeterminant c • R c (PD c : BurnolL2)=settledField c := by
  have first := (original_return_settlement observation nontrivial half).1
  have second := (original_return_settlement observation nontrivial half).2
  rw [OriginalWholeDebtRProjectionSource.original_source_action observation nontrivial half]
  unfold settledField OriginalWholeDebtRProjectionSource.sourceField
  rw [smul_sub,smul_sub,smul_sub,smul_smul,smul_smul,smul_smul]
  linear_combination (norm := module)
    (-2 : ℂ) • congrArg (fun z : ℂ => z • OriginalKSourceResolventReconstruction.generatedK (barC c)) first+
    (-2 : ℂ) • congrArg (fun z : ℂ => z • physicalOutsideColumn c) second

end OriginalWholeDebtRContactSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
