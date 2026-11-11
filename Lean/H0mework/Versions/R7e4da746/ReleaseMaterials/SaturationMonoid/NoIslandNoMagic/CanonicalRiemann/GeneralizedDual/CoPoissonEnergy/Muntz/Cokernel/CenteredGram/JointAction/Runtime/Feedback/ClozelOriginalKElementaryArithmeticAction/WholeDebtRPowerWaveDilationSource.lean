import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Source.PowerWave
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRColumnForwardSource
import H0mework.Versions.R7e4da746.Arithmetic.RieszFiniteSource.SourceProfile

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRPowerWaveDilationSource
open Complex Filter MeasureTheory Set FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFiniteSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceResolventReconstruction OriginalKFullAdjointSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open OriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKPairedBEulerJunctionSource OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open scoped InnerProductSpace Topology FourierTransform
local notation "q" => (1/4 : ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "DT" => TemperedDistribution ℝ ℂ
local notation "F" => fourierL2
local notation "K" => generatedK
local notation "U" => burnolMultiplicativeDilation
local notation "A" => pairedBurnolMultiplicativeDilation
local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "C" => correctionRaw
local notation "T" => OriginalWholeDebtRAdjointContactSource.T
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace q).isClosed.isComplete
open private actualAdjoint_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source
open private original_R_Fourier_adjoint Fourier_outside outside_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open private constant_euler from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RieszEulerDomain

def kernelMass (c : BurnolCompletedMellinCoordinate) : ℂ := ((‖K c‖^2:ℝ):ℂ)
def frequency (c : BurnolCompletedMellinCoordinate) : ℂ := c.value-1/2
def powerWave (c : BurnolCompletedMellinCoordinate) : BurnolL2 := hPowerPhysicalCorrection (barC c)

/-- Both existing signed source integrals retain their distinct whole Fourier-edge programs. -/
def singleSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  F (coupling1 c • profileIntegral (barC c) (-h)+
    coupling0 c • fourierProfileIntegral (barC c) (-h))
def pairedSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  (1/2:ℂ) • (singleSource c h+singleSource c (-h))

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : barC (barC c)=c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
private theorem kernel_even (c : BurnolCompletedMellinCoordinate) : reflectL2 (K c)=K c := by
  rw [generatedK_eq_original]
  exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
private theorem action_source (c : BurnolCompletedMellinCoordinate) :
    sourceAction c=A junctionShift (K c) := by
  rw [generatedK_eq_original]
  rfl
private theorem wave_even (c : BurnolCompletedMellinCoordinate) : reflectL2 (powerWave c)=powerWave c :=
  burnolAmbientEvenPart_even _
private theorem mass_read (c : BurnolCompletedMellinCoordinate) : inner ℂ (K c) (K c)=kernelMass c := by
  rw [inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow _ _).symm
private theorem damping_ne_zero (c : BurnolCompletedMellinCoordinate) : (damping c:ℂ)≠0 := by
  exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr c.rightHalf).ne'
private theorem damping_twice (c : BurnolCompletedMellinCoordinate) :
    c.value+star c.value-1=2*(damping c:ℂ) := by
  rw [show c.value+star c.value=(2*c.value.re:ℝ) from Complex.add_conj c.value]
  push_cast
  unfold damping
  push_cast
  ring

private theorem lift_fourier (value:BurnolL2) : 𝓕 (value:DT)=(F value:DT) :=
  Lp.fourier_toTemperedDistribution_eq _

private theorem fourier_twice_L2 (value : BurnolL2) (even : reflectL2 value=value) :
    𝓕 (𝓕 (value:DT))=(value:DT) := by
  rw [lift_fourier,lift_fourier,fourierL2_fourierL2,even]

private theorem fourier_euler (value:DT) : 𝓕 (GapEuler.euler value)=-GapEuler.euler (𝓕 value) := by
  have source:=GapEuler.euler_fourier value
  linear_combination (norm:=module) source

private theorem Psi_twice : 𝓕 (𝓕 Response.Psi)=Response.Psi := by
  have seedEven : reflectL2 ConstantDual.seed=ConstantDual.seed := by
    change reflectL2 (burnolRadiusZeroExtension q (intervalConstant q))=_
    rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
    rfl
  have seedTwice:=fourier_twice_L2 ConstantDual.seed seedEven
  have edgeRead : GapEuler.edge q=-GapEuler.euler (ConstantDual.seed:DT)-
      (1/2:ℂ) • (ConstantDual.seed:DT) := by
    have source:=constant_euler
    linear_combination (norm:=module) source
  have edgeTwice : 𝓕 (𝓕 (GapEuler.edge q))=GapEuler.edge q := by
    rw [edgeRead]
    simp only [sub_eq_add_neg,FourierTransform.fourier_neg,FourierAdd.fourier_add,
      FourierSMul.fourier_smul]
    rw [fourier_euler,FourierTransform.fourier_neg,fourier_euler,seedTwice]
    module
  unfold Response.Psi
  simp only [sub_eq_add_neg,FourierTransform.fourier_neg,FourierAdd.fourier_add]
  rw [fourier_twice_L2 Response.wholeU Response.wholeU_reflection,
    fourier_twice_L2 Response.wholeV Response.wholeV_reflection,edgeTwice]

private theorem native_adjoint (c : BurnolCompletedMellinCoordinate) :
    T (barC c) (K c)=returnRatio c • F (K (barC c))-
      (damping c:ℂ)⁻¹ • K c-(2*kernelMass c) • powerWave c := by
  rw [OriginalWholeDebtRAdjointContactSource.T,actualAdjoint_read]
  have source:=original_R_adjoint_conjugateK_generated (barC c)
  unfold sourceConjugateAdjointAction at source
  rw [conjugate_twice] at source
  simpa only [returnRatio,damping,kernelMass,powerWave,
    OriginalKCrossParameterRAdjointSource.CayleyEnergySource.sourceDamping,
    OriginalPrimitiveRankBalance.conjugateCoordinate,Complex.star_def,Complex.conj_re] using source

private theorem adjoint_kernel_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (T (barC c) (K c):DT)-frequency c • (T (barC c) (K c):DT)=
      (2:ℂ) • (K c:DT) := by
  have material:=sourceResolvent_euler (barC c) (F (K c))
  have full : sourceResolvent (barC c) (F (K c))=
      burnolDirectRightResolvent (c.value/2) (F (K c)) := by
    unfold sourceResolvent
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  have read:=original_R_Fourier_adjoint c (F (K c))
  rw [fourierL2_fourierL2,kernel_even,←actualAdjoint_read,
    ←OriginalWholeDebtRAdjointContactSource.T] at read
  have rhs : GapEuler.euler (sourceResolvent (barC c) (F (K c)):DT)=
      -(2:ℂ) • (F (K c):DT)-frequency c •
        (sourceResolvent (barC c) (F (K c)):DT) := by
    simpa only [sourceRate,frequency,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
      using eq_sub_of_add_eq material
  rw [←read,←full,←lift_fourier,GapEuler.euler_fourier,rhs]
  simp only [sub_eq_add_neg,FourierTransform.fourier_neg,FourierAdd.fourier_add,
    FourierSMul.fourier_smul]
  rw [lift_fourier,fourierL2_fourierL2,kernel_even]
  module

private theorem kernel_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (K c:DT)=Kernel.A c • Response.Psi+Kernel.beta c • 𝓕 Response.Psi-
      (star c.value-1/2) • (K c:DT) := by
  simpa only [generatedK_eq_original] using eq_sub_of_add_eq (Kernel.original_kernel_euler c)

private theorem Fourier_kernel_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (F (K (barC c)):DT)=frequency c • (F (K (barC c)):DT)-
      Kernel.beta (barC c) • Response.Psi-Kernel.A (barC c) • 𝓕 Response.Psi := by
  rw [←lift_fourier,GapEuler.euler_fourier,kernel_euler]
  simp only [sub_eq_add_neg,FourierTransform.fourier_neg,FourierAdd.fourier_add,
    FourierSMul.fourier_smul]
  rw [Psi_twice,lift_fourier]
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  unfold frequency
  module

/-- The original two native K equations generate this whole power-wave source. -/
theorem actual_power_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (((2*kernelMass c) • powerWave c:BurnolL2):DT)-
      frequency c • (((2*kernelMass c) • powerWave c:BurnolL2):DT)=
        -coupling0 c • Response.Psi-coupling1 c • 𝓕 Response.Psi := by
  have source:=adjoint_kernel_euler c
  rw [native_adjoint] at source
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (_))-
    frequency c • Lp.toTemperedDistributionCLM ℂ volume 2 (_)=_ at source
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (_))-
    frequency c • Lp.toTemperedDistributionCLM ℂ volume 2 (_)=_
  simp only [map_sub,map_smul,Lp.toTemperedDistributionCLM_apply] at source ⊢
  rw [kernel_euler,Fourier_kernel_euler] at source
  have coefficient : (damping c:ℂ)⁻¹*(c.value+star c.value-1)=2 := by
    rw [damping_twice]
    field_simp [damping_ne_zero c]
  have paid:=congrArg (fun z:ℂ=>z • (K c:DT)) coefficient
  unfold frequency at source
  unfold coupling0 coupling1 frequency
  linear_combination (norm:=module) -source+paid

private theorem Fourier_power_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (((2*kernelMass c) • F (powerWave c):BurnolL2):DT)+
      (star (barC c).value-1/2) • (((2*kernelMass c) • F (powerWave c):BurnolL2):DT)=
        coupling1 c • Response.Psi+coupling0 c • 𝓕 Response.Psi := by
  have source:=congrArg (fourierCLM ℂ DT) (actual_power_euler c)
  simp only [map_sub,map_smul,fourierCLM_apply] at source
  rw [fourier_euler,Psi_twice,lift_fourier] at source
  change -GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (_))-
    frequency c • Lp.toTemperedDistributionCLM ℂ volume 2 (_)=_ at source
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (_))+
    (star (barC c).value-1/2) • Lp.toTemperedDistributionCLM ℂ volume 2 (_)=_
  simp only [map_smul,Lp.toTemperedDistributionCLM_apply] at source ⊢
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  unfold frequency at source
  linear_combination (norm:=module) -source

private theorem profile_action (c : BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (first second:ℂ) (equation : GapEuler.euler (value:DT)+
      (star c.value-1/2) • (value:DT)=first • Response.Psi+second • 𝓕 Response.Psi) (h:ℝ) :
    U h value=Complex.exp (-(star c.value-1/2)*(h:ℂ)) • value+
      first • profileIntegral c h+second • fourierProfileIntegral c h := by
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot («F» := ℂ) (μ := volume))
  ext test
  let read := fun t:ℝ=>(U t value:DT) test
  let firstRead := fun t:ℝ=>Response.Psi (coPoissonSchwartzEnergyTranslation (-t) test)
  let secondRead := fun t:ℝ=>(𝓕 Response.Psi) (coPoissonSchwartzEnergyTranslation (-t) test)
  have derivative (t:ℝ) : HasDerivAt read
      ((first*firstRead t+second*secondRead t)-(star c.value-1/2)*read t) t := by
    have source:=congrArg (fun v:DT=>v (coPoissonSchwartzEnergyTranslation (-t) test)) equation
    simp only [add_apply,smul_apply,smul_eq_mul] at source
    have actual:=Dilation.original_weak_derivative value test t
    rw [OriginalRieszFiniteResponse.original_euler_action,eq_sub_of_add_eq source] at actual
    rw [←OriginalRieszFiniteResponse.original_read value test t] at actual
    exact actual
  have regular:=((profileRead_continuous c test).const_mul first).add
    ((fourierProfileRead_continuous c test).const_mul second)
  have generated:=_root_.OriginalRieszFiniteResponse.Integration.finite_response read
    (fun t=>first*firstRead t+second*secondRead t) (star c.value-1/2) derivative regular h
  have firstInt:=profileRead_integrable c test h
  have secondInt:=fourierProfileRead_integrable c test h
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (U h value)) test=
    (Lp.toTemperedDistributionCLM ℂ volume 2
      (Complex.exp (-(star c.value-1/2)*(h:ℂ)) • value+
        first • profileIntegral c h+second • fourierProfileIntegral c h)) test
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,Lp.toTemperedDistributionCLM_apply]
  rw [profileIntegral_read,fourierProfileIntegral_read,←intervalIntegral.integral_const_mul,
    ←intervalIntegral.integral_const_mul,add_assoc,
    ←intervalIntegral.integral_add (firstInt.const_mul first)
      (secondInt.const_mul second)]
  have base : read 0=(value:DT) test := by
    simp only [read,burnolMultiplicativeDilation_zero]
  rw [base] at generated
  convert generated using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [firstRead,secondRead]
  ring

theorem actual_single_action (c : BurnolCompletedMellinCoordinate) (h:ℝ) :
    (2*kernelMass c) • U h (powerWave c)=
      (2*kernelMass c*Complex.exp (frequency c*(h:ℂ))) • powerWave c+singleSource c h := by
  have source:=profile_action (barC c) ((2*kernelMass c) • F (powerWave c))
    (coupling1 c) (coupling0 c) (Fourier_power_euler c) (-h)
  have acted:=congrArg F source
  simp only [map_add,map_smul,fourierL2_burnolMultiplicativeDilation,neg_neg,
    fourierL2_fourierL2,wave_even] at acted
  change _= _+coupling1 c • F (profileIntegral (barC c) (-h))+
    coupling0 c • F (fourierProfileIntegral (barC c) (-h)) at acted
  have weight : Complex.exp (-(star (barC c).value-1/2)*((-h:ℝ):ℂ))=
      Complex.exp (frequency c*(h:ℂ)) := by
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,Complex.ofReal_neg,
      neg_mul_neg,frequency]
  rw [weight] at acted
  unfold singleSource
  simp only [map_add,map_smul]
  convert acted using 1; module

/-- Both signed source programs generate the original paired action with its full unit. -/
theorem actual_pair_action (c : BurnolCompletedMellinCoordinate) (h:ℝ) :
    (2*kernelMass c) • A h (powerWave c)=
      (2*kernelMass c*pairedMellinTranslationCharacter c.value h) • powerWave c+pairedSource c h := by
  have positive:=actual_single_action c h
  have negative:=actual_single_action c (-h)
  have character : pairedMellinTranslationCharacter c.value h=
      (Complex.exp (frequency c*(h:ℂ))+Complex.exp (frequency c*((-h:ℝ):ℂ)))/2 := by
    unfold pairedMellinTranslationCharacter fullMellinTranslationCharacter
      reciprocalMellinTranslationCharacter frequency
    rw [Complex.ofReal_neg]
    congr 1
    have rate : ((1/2:ℂ)-c.value)*(h:ℂ)=(c.value-1/2)*(-(h:ℂ)) := by ring
    rw [rate]
    ring
  rw [character]
  unfold pairedBurnolMultiplicativeDilation pairedSource
  change (2*kernelMass c) • ((1/2:ℂ) • (U h (powerWave c)+U (-h) (powerWave c)))=_
  linear_combination (norm:=module) (1/2:ℂ) • positive+(1/2:ℂ) • negative

private theorem paired_symmetric (h:ℝ) (left right:BurnolL2) :
    inner ℂ (A h left) right=inner ℂ left (A h right) := by
  have positive:=(U h).inner_map_eq_flip left right
  have negative:=(U (-h)).inner_map_eq_flip left right
  rw [←burnolMultiplicativeDilation_neg_eq_symm] at positive negative
  rw [neg_neg] at negative
  unfold pairedBurnolMultiplicativeDilation
  change inner ℂ ((1/2:ℂ) • (U h left+U (-h) left)) right=
    inner ℂ left ((1/2:ℂ) • (U h right+U (-h) right))
  simp only [inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,
    map_div₀,map_one,map_ofNat]
  linear_combination (1/2:ℂ)*positive+(1/2:ℂ)*negative

private theorem rho_read (c : BurnolCompletedMellinCoordinate) :
    inner ℂ (C c) (physicalOutsideColumn c)=
      inner ℂ (F (K c)) (A junctionShift (powerWave c)) := by
  have killed : inner ℂ (P (sourceAction c):BurnolL2) (physicalOutsideColumn c)=0 := by
    exact outsideColumn_orthogonal c _ (P (sourceAction c)).property
  rw [source_action_projection,inner_sub_left] at killed
  have paired:=fourierL2.inner_map_map (K c) (A junctionShift (physicalOutsideColumn c))
  rw [←pairedBurnolMultiplicativeDilation_fourier] at paired
  unfold physicalOutsideColumn at paired
  rw [fourierL2.apply_symm_apply] at paired
  change inner ℂ (F (K c)) (A junctionShift (powerWave c))=
    inner ℂ (K c) (A junctionShift (physicalOutsideColumn c)) at paired
  rw [action_source] at killed
  rw [paired_symmetric] at killed
  linear_combination -killed-paired

/-- The original C and the same source S jointly pay the whole top-return column price. -/
theorem rho_return (c : BurnolCompletedMellinCoordinate) :
    (2*kernelMass c)*inner ℂ (C c) (physicalOutsideColumn c)=
      inner ℂ (F (K c)) (pairedSource c junctionShift) := by
  have source:=congrArg (fun v:BurnolL2=>inner ℂ (F (K c)) v)
    (actual_pair_action c junctionShift)
  have killed : inner ℂ (F (K c)) (powerWave c)=0 := by
    have physical : K c∈evenBurnolClosedFace q := by
      rw [generatedK_eq_original]
      exact (burnolCompletedMellinRieszVector c).property
    exact powerCorrection_orthogonal (barC c) _ (fourierL2_mem_evenBurnolClosedFace physical)
  rw [inner_smul_right,inner_add_right,inner_smul_right,killed,mul_zero,zero_add,←rho_read] at source
  exact source

private theorem source_price (c : BurnolCompletedMellinCoordinate) :
    OriginalWholeDebtRQuarterUnitSettlementSource.sourcePrice c=
      2*pairedMellinTranslationCharacter c.value junctionShift*kernelMass c-
        2*inner ℂ (K c) (sourceAction c) := by
  have nn : 0≤junctionShift := junctionShift_pos.le
  have source:=forcing_pair_source c junctionShift nn
  have price:=(OriginalWholeDebtRNativeForcingSource.actual_finite_price c).trans
    (OriginalWholeDebtRQuarterUnitSettlementSource.actual_finite_price_source c)
  rw [BandFiniteSourcePrice.source_pair_finite_price c junctionShift nn,
    price] at source
  have forward:=original_finite_action c junctionShift
  have backward:=original_finite_action c (-junctionShift)
  rw [←generatedK_eq_original] at forward backward source
  have paired : inner ℂ (sourceAction c) (K c)=inner ℂ (K c) (sourceAction c) := by
    rw [action_source]
    exact paired_symmetric junctionShift (K c) (K c)
  have sum : forcingIntegral c junctionShift+forcingIntegral c (-junctionShift)=
      (2:ℂ) • sourceAction c-
        (2*pairedMellinTranslationCharacter (star c.value) junctionShift) • K c := by
    rw [action_source]
    unfold pairedBurnolMultiplicativeDilation pairedMellinTranslationCharacter
      fullMellinTranslationCharacter reciprocalMellinTranslationCharacter
    unfold fullMellinTranslationCharacter at forward backward
    simp only [Complex.ofReal_neg] at backward
    have negativeRate : ((1/2:ℂ)-star c.value)*(-(junctionShift:ℂ))=
        (star c.value-1/2)*(junctionShift:ℂ) := by ring
    rw [negativeRate] at backward
    change forcingIntegral c junctionShift+forcingIntegral c (-junctionShift)=
      (2:ℂ) • ((1/2:ℂ) • (U junctionShift (K c)+U (-junctionShift) (K c)))-_
    linear_combination (norm:=module) -forward-backward
  rw [sum,inner_sub_left,inner_smul_left,inner_smul_left,mass_read,paired] at source
  have character : star (pairedMellinTranslationCharacter (star c.value) junctionShift)=
      pairedMellinTranslationCharacter c.value junctionShift := by
    simp [pairedMellinTranslationCharacter,fullMellinTranslationCharacter,
      reciprocalMellinTranslationCharacter,←Complex.exp_conj,map_ofNat]
  simp only [starRingEnd_apply,star_mul,star_ofNat,character] at source
  linear_combination source

private theorem adjoint_paired (c : BurnolCompletedMellinCoordinate) (h:ℝ) (value:BurnolL2) :
    T (barC c) (A h value)=A h (T (barC c) value) := by
  apply ext_inner_left ℂ
  intro test
  rw [OriginalWholeDebtRAdjointContactSource.T,ContinuousLinearMap.adjoint_inner_right,
    ←paired_symmetric]
  have commute : A h (burnolDirectRightResolventCLM (barC c) test)=
      burnolDirectRightResolventCLM (barC c) (A h test) := by
    unfold pairedBurnolMultiplicativeDilation
    simp only [smul_apply,add_apply,map_smul,map_add]
    change (1/2:ℂ) • (U h (burnolDirectRightResolvent ((barC c).value/2) test)+
      U (-h) (burnolDirectRightResolvent ((barC c).value/2) test))=
        (1/2:ℂ) • (burnolDirectRightResolvent ((barC c).value/2) (U h test)+
          burnolDirectRightResolvent ((barC c).value/2) (U (-h) test))
    rw [burnolDirectRightResolvent_dilation,burnolDirectRightResolvent_dilation]
  rw [commute,←ContinuousLinearMap.adjoint_inner_right,paired_symmetric]

private theorem correction_outside (c : BurnolCompletedMellinCoordinate) : O (sourceAction c)=C c := by
  rw [outside_eq,source_action_projection]
  module

/-- The same finite source retains the complete original source price as an actual L² unit field. -/
theorem actual_price_unit (c : BurnolCompletedMellinCoordinate) :
    OriginalWholeDebtRQuarterUnitSettlementSource.sourcePrice c • powerWave c=
      returnRatio c • F (C (barC c))-(damping c:ℂ)⁻¹ • C c-
        O (pairedSource c junctionShift)-
        O (OriginalWholeDebtRAdjointContactSource.sourceField c (barC c)) := by
  let physical : BurnolPaAmbientCarrier:=P (sourceAction c)
  have split : sourceAction c=C c+(physical:BurnolL2) := by
    change sourceAction c=C c+(P (sourceAction c):BurnolL2)
    rw [source_action_projection]
    module
  have native:=congrArg O (adjoint_paired c junctionShift (K c))
  rw [←action_source] at native
  rw [split,map_add,map_add,OriginalWholeDebtRAdjointContactSource.actual_source_action,
    native_adjoint] at native
  simp only [map_sub,map_smul] at native
  rw [pairedBurnolMultiplicativeDilation_fourier,←Fourier_outside,
    ←action_source,←action_source,correction_outside,correction_outside] at native
  have physicalRead:=physical_adjoint_full_defect (barC c) physical
  rw [←actualAdjoint_read,←OriginalWholeDebtRAdjointContactSource.T] at physicalRead
  rw [←outside_eq] at physicalRead
  change O (T (barC c) (physical:BurnolL2))=physicalAmplitude (barC c) physical • powerWave c at physicalRead
  have amplitude : physicalAmplitude (barC c) physical=-2*inner ℂ (K c) (sourceAction c) := by
    rw [←outsidePhysicalSource_read,outsidePhysicalSource,conjugate_twice,inner_smul_left]
    have projected:=(evenBurnolClosedFace q).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (burnolCompletedMellinRieszVector c) (sourceAction c)
    change inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2)
      (P (sourceAction c):BurnolL2)=
        inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2) (sourceAction c) at projected
    rw [←generatedK_eq_original] at projected
    change inner ℂ (K c) (physical:BurnolL2)=inner ℂ (K c) (sourceAction c) at projected
    rw [projected]
    simp [map_ofNat]
  rw [amplitude] at physicalRead
  have waveOutside : O (powerWave c)=powerWave c :=
    Submodule.starProjection_eq_self_iff.mpr (powerCorrection_orthogonal (barC c))
  have full:=congrArg O (actual_pair_action c junctionShift)
  rw [map_smul,map_add,map_smul,waveOutside] at full
  rw [physicalRead] at native
  rw [source_price]
  linear_combination (norm:=module) native-full

end OriginalWholeDebtRPowerWaveDilationSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
