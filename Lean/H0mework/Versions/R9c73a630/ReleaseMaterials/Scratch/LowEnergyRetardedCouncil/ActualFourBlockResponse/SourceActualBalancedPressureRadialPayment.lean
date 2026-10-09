import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPressureProductCrossPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualNativeInvoiceSourceReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPressureFixedReturnPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualNonmagneticRadialCrossPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualBalancedPressureRadialPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm SourcePhysicalKineticSquare ActualUnweightedSquareCurrentPayment
open SourceScalarVirialBulk SourceScalarGaugeScale SourceCoframeVolumeCurrent SourceHamiltonianScaleJet
open SourceNativeCutoffContact SourceQuantumScalarChart SourceScalarInverseNativeEnergy
open ActualBalancedFixedContactPayment ActualBalancedPressureWardPayment ActualSecondPressureMagneticPayment
open ActualNonmagneticRadialCrossPayment ActualNonmagneticPressureStorage ActualMixedWindowGram
open ActualPhaseBulkSquare ActualScalarPhaseJet ActualVectorJointCost SourceResolventBandLimit
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent GaussNativeEnergy SourcePhysicalHamiltonianSquare
open SourceRetardedGraph SourceClockReflectedForm SourceScalarNativeComparison SourceScalarInverseBulk
open ActualTwoResolventCascade ActualRawResidualTailPayment
open ActualMixedCovarianceTail
open ActualBalancedPressureMomentPayment ActualPressureFixedReturnPayment
open Lean Meta Elab Term MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End:=QuantumTest →ₗ[ℂ]QuantumTest
attribute [local irreducible] sourcePair nonmagneticSecondField shiftedSquare phaseForce thetaAction
  balancedPressureJet radialDouble
  scalarKinetic gaugeKinetic centeredAction vacuumLinearAction inverseVolumeAction
  ActualBalancedLocalizationContactReturn.balancedGenerator compressionCore resolventCore diagonalAction phaseCoefficient

elab "paid_pressure_radial%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualNonmagneticRadialCrossPayment 0) "LowEnergy")
    "ActualNonmagneticRadialCrossPayment") field.getId.eraseMacroScopes.toString)
elab "paid_pressure_ward_radial%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureWardPayment 0) "LowEnergy")
    "ActualBalancedPressureWardPayment") field.getId.eraseMacroScopes.toString)
elab "paid_pressure_radial_ims%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarBulkResidualBudget 0) "LowEnergy")
    "SourceScalarBulkResidualBudget") field.getId.eraseMacroScopes.toString)

def pressureRadialRemainder:End:=
  (phaseCoefficient:ℂ) •
    (((-36:ℂ) • gaugeKinetic+(48:ℂ) • centeredAction-(54:ℂ) • vacuumLinearAction)*inverseVolumeAction+
      inverseVolumeAction*((-36:ℂ) • gaugeKinetic+(48:ℂ) • centeredAction-(54:ℂ) • vacuumLinearAction))

attribute [local irreducible] pressureRadialRemainder

/-- Native and phase-force source weights coincide at thirty; the full
vacuum-affine remainder is retained as actual commuting multipliers. -/
theorem actual_pressure_radial_source:
    balancedPressureJet nonmagneticSecondField=(30:ℂ) • nonmagneticSecondField+
      pressureRadialRemainder:=by
  have h:=actual_balanced_pressure_source
  unfold nonmagneticSecondField nonmagneticBulk at h ⊢
  unfold pressureRadialRemainder
  rw [(paid_pressure_ward_radial% shifted_source)] at h ⊢
  simp only [add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,
    smul_add,smul_sub,smul_smul] at h ⊢
  linear_combination (norm:=module) h

private theorem commuting_remainder(T G C V U:End)(c:ℂ)
    (hG:Commute G T)(hC:Commute C T)(hV:Commute V T)(hU:Commute U T):
    Commute (c • (((-36:ℂ) • G+(48:ℂ) • C-(54:ℂ) • V)*U+
      U*((-36:ℂ) • G+(48:ℂ) • C-(54:ℂ) • V))) T:=by
  change _*T=T*_
  simp only [add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
  rw [(paid_pressure_radial% product_commute) G U T hG.eq hU.eq,
    (paid_pressure_radial% product_commute) U G T hU.eq hG.eq,
    (paid_pressure_radial% product_commute) C U T hC.eq hU.eq,
    (paid_pressure_radial% product_commute) U C T hU.eq hC.eq,
    (paid_pressure_radial% product_commute) V U T hV.eq hU.eq,
    (paid_pressure_radial% product_commute) U V T hU.eq hV.eq]

theorem actual_pressure_radial_remainder_commute(m ell:ℕ):
    Commute pressureRadialRemainder (thetaAction m ell):=by
  have hg:Commute gaugeKinetic (thetaAction m ell):=(paid_pressure_radial_ims% gauge_theta) m ell
  have hu:Commute inverseVolumeAction (thetaAction m ell):=by
    apply LinearMap.ext
    intro f
    simp only [Module.End.mul_apply]
    exact (paid_radial_square% theta_inverse) m ell f
  have hc:Commute centeredAction (thetaAction m ell):=by
    unfold centeredAction
    exact ((paid_pressure_radial_ims% theta_real_commute) m ell _ _).symm
  have hl:Commute vacuumLinearAction (thetaAction m ell):=by
    unfold vacuumLinearAction
    exact ((paid_pressure_radial_ims% theta_real_commute) m ell _ _).symm
  unfold pressureRadialRemainder
  exact commuting_remainder (thetaAction m ell) gaugeKinetic centeredAction vacuumLinearAction
    inverseVolumeAction (phaseCoefficient:ℂ) hg hc hl hu

theorem actual_pressure_radial_double(m ell:ℕ):
    radialDouble m ell (balancedPressureJet nonmagneticSecondField)=
      (30:ℂ) • radialDouble m ell nonmagneticSecondField:=by
  rw [actual_pressure_radial_source,(paid_pressure_radial% double_add),
    (paid_pressure_radial% double_smul),
    (paid_pressure_radial% double_zero_of_commute) m ell pressureRadialRemainder
      (actual_pressure_radial_remainder_commute m ell),add_zero]

private theorem pair_sub_right(f h k:QuantumTest):sourcePair f (h-k)=sourcePair f h-sourcePair f k:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_add_right(f h k:QuantumTest):sourcePair f (h+k)=sourcePair f h+sourcePair f k:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul_right(a:ℂ)(f h:QuantumTest):sourcePair f (a • h)=a*sourcePair f h:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem theta_pair(m ell:ℕ)(f h:QuantumTest):
    sourcePair f (thetaAction m ell h)=sourcePair (thetaAction m ell f) h:=by
  unfold thetaAction
  exact multiply_pair _ _ _ _
private theorem pair_sub_left(f h k:QuantumTest):sourcePair (f-h) k=sourcePair f k-sourcePair h k:=by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pressure_pair(f h:QuantumTest):
    sourcePair f (balancedPressureJet nonmagneticSecondField h)=
      sourcePair (balancedPressureJet nonmagneticSecondField f) h:=by
  have hA(a b:QuantumTest):sourcePair a (ActualBalancedLocalizationContactReturn.balancedGenerator b)=
      -sourcePair (ActualBalancedLocalizationContactReturn.balancedGenerator a) b:=
    (paid_pressure_ward_radial% generator_skew) a b
  have hS:=actual_nonmagnetic_source_pair
  unfold balancedPressureJet
  simp only [Module.End.mul_apply,LinearMap.sub_apply,pair_sub_right,pair_sub_left]
  rw [hA f (nonmagneticSecondField h),hS f (ActualBalancedLocalizationContactReturn.balancedGenerator h),
    ←hS (ActualBalancedLocalizationContactReturn.balancedGenerator f) h,
    hA (nonmagneticSecondField f) h]
  ring

/-- Both theta orders survive until the Hermitian source pair is applied. -/
theorem actual_pressure_radial_jordan(m ell:ℕ)(f:QuantumTest):
    (sourcePair (thetaAction m ell f)
      ((thetaAction m ell*balancedPressureJet nonmagneticSecondField-
        balancedPressureJet nonmagneticSecondField*thetaAction m ell) f)).re=
      (1/2:ℝ)*(sourcePair f (radialDouble m ell (balancedPressureJet nonmagneticSecondField) f)).re:=by
  rw [(paid_pressure_radial% double_pair)]
  simp only [Module.End.mul_apply,LinearMap.sub_apply,pair_sub_right]
  rw [theta_pair]
  have hr:(sourcePair f (balancedPressureJet nonmagneticSecondField
      (thetaAction m ell (thetaAction m ell f)))).re=
      (sourcePair (thetaAction m ell (thetaAction m ell f))
        (balancedPressureJet nonmagneticSecondField f)).re:=by
    rw [pressure_pair]
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) _ _
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.re_ofNat,
    Complex.im_ofNat,zero_mul,sub_zero]
  rw [hr]
  ring

elab "paid_pressure_second%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiSecondPressure 0) "LowEnergy")
    "SourceClockPhiSecondPressure") field.getId.eraseMacroScopes.toString)

def centeredRoot(f:QuantumTest):ℝ:=
  (sourcePair (inverseRootAction f) (centeredAction (inverseRootAction f))).re

/-- The actual thirty/native, thirty-six/gauge and thirty/force weights
are evaluated before absorption, including both scalar field inventories. -/
theorem actual_pressure_source_energy(f:QuantumTest):
    (sourcePair f (balancedPressureJet nonmagneticSecondField f)).re=
      -60*phaseCoefficient*sourceTime 0*inverseNativeEnergy f-
      432*phaseCoefficient*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re-
      120*‖embed (phaseForce f)‖^2-
      12*phaseCoefficient*sourceTime 0*shiftedMoment f-
      12*phaseCoefficient*centeredRoot f+
      3*phaseCoefficient*sourceTime 0*‖vacuum‖^2*‖embed f‖^2:=by
  have h:=congrArg (fun X:End=>(sourcePair f (X f)).re) actual_balanced_pressure_source
  have hs:=(paid_pressure_ward_radial% weighted_pair) scalarKinetic (paid_pressure_storage% root_scalar) f
  have hg:=(paid_pressure_ward_radial% weighted_pair) gaugeKinetic inverse_root_electric f
  have hc:=(paid_pressure_ward_radial% weighted_pair) centeredAction (by
    unfold centeredAction
    exact inverse_root_real _ _) f
  have hS:=actual_nonmagnetic_storage_source f
  have hK:=(paid_pressure_second% scalar_root_form) f
  have hN:scalarForm (inverseVolumeAction f)=inverseNativeEnergy f:=by
    change nativeScalarEnergy (inverseVolumeAction f)=inverseNativeEnergy f
    exact original_inverse_native_return f
  have hH:=actual_phase_force_square_energy f
  simp only [Module.End.mul_apply] at hH
  have hPC:=actual_phase_coefficient_positive
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_right,pair_smul_right,
    Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,mul_zero,sub_zero] at h
  have hsre:=congrArg Complex.re hs
  have hgre:=congrArg Complex.re hg
  have hcre:=congrArg Complex.re hc
  simp only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] at hsre hgre hcre
  norm_num only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.im_ofNat,Complex.re_ofNat,zero_mul,mul_zero,add_zero,sub_zero] at h
  rw [hsre,hgre,hcre,hK,hN] at h
  simp only [Module.End.mul_apply] at h
  rw [hH] at h
  unfold nonmagneticStorage at hS
  rw [hN] at hS
  unfold centeredRoot
  field_simp [hPC.ne'] at hS
  nlinarith only [h,hS,hH]

private theorem mu_positive:0<sourceMu:=lt_of_lt_of_le zero_lt_one source_mu_large
private theorem lapse_positive:0<sourceTime 0:=by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

def nativePressureGain(sharp:Bool)(f:QuantumTest):ℝ:=
  (3*coefficientCost sharp/(16*sourceMu))*inverseNativeEnergy f+
  (27*coefficientCost sharp/(8*sourceTime 0*sourceMu))*
    (sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re+
  (9*coefficientCost sharp/(8*sourceTime 0*sourceMu*phaseCoefficient))*‖embed (phaseForce f)‖^2+
  (39*coefficientCost sharp*‖vacuum‖^2/(64*sourceMu)+9*sourceMu/4)*‖embed f‖^2

def remainingFieldDebit(sharp:Bool)(f:QuantumTest):ℝ:=
  (3*coefficientCost sharp/(16*sourceMu))*(shiftedMoment f+centeredRoot f/sourceTime 0)

/-- The same raw normalization internally absorbs all native, gauge and
phase-force departments; only the explicit original scalar field debit remains. -/
theorem actual_retarded_pressure_three_gain(sharp:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    let w:=thetaAction m ell q
    (3/4:ℝ)*(2/sourceMu)*sourceReserve sharp m ell q+
      (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*‖embed (phaseForce w)‖^2+
      (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)/12)*
        (sourcePair w (balancedPressureJet nonmagneticSecondField w)).re=
      nativePressureGain sharp w-remainingFieldDebit sharp w:=by
  dsimp only
  rw [actual_pressure_source_energy]
  unfold sourceReserve bulkCoefficient nativePressureGain remainingFieldDebit
  dsimp only
  field_simp [mu_positive.ne',lapse_positive.ne',actual_phase_coefficient_positive.ne']
  ring

attribute [local irreducible] nativePressureGain remainingFieldDebit sourceReserve bulkCoefficient
  coreWindow pressureCFCurrent pressureRadialCurrent movingPressureOperator coreCovariance

elab "paid_pressure_window%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWindowGram 0) "LowEnergy")
    "ActualMixedWindowGram") field.getId.eraseMacroScopes.toString)
elab "paid_pressure_moment_source%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureMomentPayment 0) "LowEnergy")
    "ActualBalancedPressureMomentPayment") field.getId.eraseMacroScopes.toString)

private theorem covariance_pair(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    sourcePair f (coreCovariance m ell F z hz h)=
      sourcePair (coreWindow m ell F z hz f) (coreWindow m ell F z hz h):=by
  rw [(paid_pressure_window% window_product)]
  simp only [Module.End.mul_apply]
  exact (paid_pressure_window% window_pair) m ell F z hz f (coreWindow m ell F z hz h)

/-- CF and radial are returned together, preserving both theta orders. -/
theorem actual_whole_moving_pressure_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    sourcePair g ((pressureCFCurrent m ell F z hz-pressureRadialCurrent m ell F z hz) g)=
      sourcePair (coreWindow m ell F z hz g)
        (balancedPressureJet nonmagneticSecondField (coreWindow m ell F z hz g))-
      sourcePair (coreWindow m ell F z hz g)
        (coreWindow m ell F z hz (balancedPressureJet nonmagneticSecondField g)):=by
  have h:=actual_moving_pressure_source_return m ell F z hz
  have he:pressureCFCurrent m ell F z hz-pressureRadialCurrent m ell F z hz=
      movingPressureOperator m ell F z hz-
        coreCovariance m ell F z hz*balancedPressureJet nonmagneticSecondField:=by
    linear_combination (norm:=module) h
  rw [he,LinearMap.sub_apply,pair_sub_right]
  simp only [Module.End.mul_apply]
  rw [(paid_pressure_moment_source% moving_pressure_pair),covariance_pair]
  simp only [coreWindow,Module.End.mul_apply]

/-- The positive source reserve pays the whole moving pressure current's
native, gauge and force slots; its fixed window pair and scalar field bill
remain exact source responsibilities. -/
theorem actual_whole_moving_pressure_three_gain(sharp:Bool)(m ell:ℕ)(F:Index)
    (z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    let w:=coreWindow m ell F z hz g
    (3/4:ℝ)*(2/sourceMu)*sourceReserve sharp m ell q+
      (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*‖embed (phaseForce w)‖^2+
      (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)/12)*
        (sourcePair g ((pressureCFCurrent m ell F z hz-pressureRadialCurrent m ell F z hz) g)).re=
      nativePressureGain sharp w-remainingFieldDebit sharp w-
      (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)/12)*
        (sourcePair w (coreWindow m ell F z hz (balancedPressureJet nonmagneticSecondField g))).re:=by
  dsimp only
  rw [actual_whole_moving_pressure_source,Complex.sub_re]
  have hw:coreWindow m ell F z hz g=thetaAction m ell (resolventCore F z hz g):=by
    simp only [coreWindow,Module.End.mul_apply]
  have hp:=actual_retarded_pressure_three_gain sharp m ell F z hz g
  dsimp only at hp
  rw [←hw] at hp
  nlinarith only [hp]

elab "paid_bpr_fixed%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedFixedContactPayment 0) "LowEnergy")
    "ActualBalancedFixedContactPayment") field.getId.eraseMacroScopes.toString)
elab "paid_bpr_moment%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardMomentTail 0) "LowEnergy")
    "ActualMixedWardMomentTail") field.getId.eraseMacroScopes.toString)
private theorem causal_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(ω:ℝ):
    (causalFrequency advanced μ ω).im≠0:=by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'
private def fixedPressureWindow(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)
    (g:QuantumTest)(ω:ℝ):ℂ:=
  sourcePair (coreWindow m ell F (causalFrequency advanced μ ω) (causal_nonreal advanced μ hμ ω) g)
    (coreWindow m ell F (causalFrequency advanced μ ω) (causal_nonreal advanced μ hμ ω)
      (balancedPressureJet nonmagneticSecondField g))
private theorem fixed_pressure_window_tail(μ:ℝ)(hμ:0<μ)(g:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fixedPressureWindow advanced μ hμ m ell F g) ∧
          ‖∫ω:ℝ,fixedPressureWindow advanced μ hμ m ell F g ω‖ ≤ ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=(paid_bpr_moment% window_pair_tail) μ hμ g
    (balancedPressureJet nonmagneticSecondField g) ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  let v:=fixedPressureWindow advanced μ hμ m ell F g
  have he(ω:ℝ):v ω=(paid_fixed_contact% windowPair) m ell F (causalFrequency advanced μ ω)
      g (balancedPressureJet nonmagneticSecondField g):=by
    unfold v fixedPressureWindow
    exact (paid_bpr_fixed% window_pair_return) m ell F _ _ _ _
  have hp:(∫⁻ω:ℝ,ENNReal.ofReal ‖v ω‖)≤ENNReal.ofReal ε:=by
    simp_rw [he]
    exact hF advanced
  have hi:Integrable v:=by
    refine ⟨?_,?_⟩
    · have hc:Continuous v:=by
        change Continuous (fun ω:ℝ=>v ω)
        simp_rw [he]
        exact (paid_bpr_fixed% window_pair_continuous) advanced μ hμ m ell F g
          (balancedPressureJet nonmagneticSecondField g)
      exact hc.aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_norm]
      exact lt_of_le_of_lt hp ENNReal.ofReal_lt_top
  refine ⟨hi,?_⟩
  apply (norm_integral_le_lintegral_norm v).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hp).trans_eq (ENNReal.toReal_ofReal hε.le)

private def rawCoefficient(sharp:Bool):ℝ:=3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)
private theorem raw_coefficient_source(sharp:Bool):
    3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)=rawCoefficient sharp:=rfl

def clearedNativeWork(advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(ω:ℝ):ℝ:=
  let z:=causalFrequency advanced sourceMu ω
  let hz:=causal_nonreal advanced sourceMu mu_positive ω
  let w:=coreWindow m ell F z hz g
  nativePressureGain sharp w-remainingFieldDebit sharp w+
    rawCoefficient sharp*retardedPressureSource m ell F z hz g-
    rawCoefficient sharp*(phaseCoefficient*sourceTime 0*‖vacuum‖^2/4)*‖embed w‖^2

attribute [local irreducible] rawCoefficient clearedNativeWork fixedPressureWindow
  retardedPressureSource ActualPressureProductCrossPayment.movingCurrentInvoice
elab "paid_bpr_raw%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualRawResidualTailPayment 0) "LowEnergy")
    "ActualRawResidualTailPayment") field.getId.eraseMacroScopes.toString)
elab "paid_bpr_force%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBulkCurrentSquareReturn 0) "LowEnergy")
    "ActualBulkCurrentSquareReturn") field.getId.eraseMacroScopes.toString)
private theorem raw_core_return(advanced:Bool)(F:Index)(g:QuantumTest)(ω:ℝ):
    (paid_bpr_raw% causalCore) advanced F g ω=resolventCore F (causalFrequency advanced sourceMu ω)
      (causal_nonreal advanced sourceMu mu_positive ω) g:=rfl
private theorem force_core_return(advanced:Bool)(F:Index)(g:QuantumTest)(ω:ℝ):
    (paid_bpr_force% causalCore) advanced F g ω=resolventCore F (causalFrequency advanced sourceMu ω)
      (causal_nonreal advanced sourceMu mu_positive ω) g:=rfl
private theorem cleared_native_work_return(advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(ω:ℝ):
    clearedNativeWork advanced sharp m ell F g ω=
      rawCoefficient sharp*ActualPressureProductCrossPayment.movingCurrentInvoice
        advanced sourceMu mu_positive m ell F g ω+
      (3/4:ℝ)*(2/sourceMu)*reserveFrequency advanced sharp m ell F g ω+
      (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*
        ActualBulkCurrentSquareReturn.forceResponse advanced m ell F g ω+
      (rawCoefficient sharp/12)*(fixedPressureWindow advanced sourceMu mu_positive m ell F g ω).re:=by
  have hp:=actual_whole_moving_pressure_three_gain sharp m ell F
    (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g
  dsimp only at hp
  have hC:-pressureRadialCurrent m ell F (causalFrequency advanced sourceMu ω)
      (causal_nonreal advanced sourceMu mu_positive ω)+
      pressureCFCurrent m ell F (causalFrequency advanced sourceMu ω)
        (causal_nonreal advanced sourceMu mu_positive ω)=
      pressureCFCurrent m ell F (causalFrequency advanced sourceMu ω)
        (causal_nonreal advanced sourceMu mu_positive ω)-
      pressureRadialCurrent m ell F (causalFrequency advanced sourceMu ω)
        (causal_nonreal advanced sourceMu mu_positive ω):=by module
  unfold clearedNativeWork rawCoefficient ActualPressureProductCrossPayment.movingCurrentInvoice
    fixedPressureWindow reserveFrequency ActualBulkCurrentSquareReturn.forceResponse
  dsimp only
  rw [hC]
  simp only [coreWindow,Module.End.mul_apply] at hp ⊢
  rw [raw_core_return,force_core_return]
  nlinarith only [hp]

private def causalNative(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(ω:ℝ):ℂ:=
  ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F (causalFrequency advanced sourceMu ω)
    (causal_nonreal advanced sourceMu mu_positive ω) g
private def causalRadial(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(ω:ℝ):ℂ:=
  ActualShiftedQuadraticWardPayment.radialResponseCorrection m ell F (causalFrequency advanced sourceMu ω)
    (causal_nonreal advanced sourceMu mu_positive ω) g
private def causalCorrected(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(ω:ℝ):ℂ:=
  ActualUnweightedSquareCurrentPayment.shiftedResponse advanced m ell F g ω-
    causalNative advanced m ell F g ω-causalRadial advanced m ell F g ω
attribute [local irreducible] ActualShiftedQuadraticWardPayment.shiftedSquare phaseSecond
  ActualPhaseWardIntertwiner.shiftedInverseWard ActualUnweightedSquareCurrentPayment.shiftedResponse
  causalCorrected causalNative causalRadial

elab "paid_bpr_unweighted%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualUnweightedSquareCurrentPayment 0) "LowEnergy")
    "ActualUnweightedSquareCurrentPayment") field.getId.eraseMacroScopes.toString)
private theorem unweighted_core_return(advanced:Bool)(F:Index)(g:QuantumTest)(ω:ℝ):
    (paid_bpr_unweighted% causalCore) advanced F g ω=resolventCore F (causalFrequency advanced sourceMu ω)
      (causal_nonreal advanced sourceMu mu_positive ω) g:=rfl
private theorem causal_corrected_tail(g:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (causalCorrected advanced m ell F g) ∧
          ‖∫ω:ℝ,causalCorrected advanced m ell F g ω‖ ≤ ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=ActualShiftedQuadraticWardPayment.actual_corrected_shifted_response_tail g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have hf:=hF advanced
  dsimp only at hf
  have hB:ActualUnweightedSquareCurrentPayment.shiftedSquare=
      ActualShiftedQuadraticWardPayment.shiftedSquare:=by
    unfold ActualUnweightedSquareCurrentPayment.shiftedSquare ActualShiftedQuadraticWardPayment.shiftedSquare
    rfl
  have hfun:(fun ω:ℝ=>sourcePair
      (coreWindow m ell F (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g)
      (ActualShiftedQuadraticWardPayment.shiftedSquare
        (coreWindow m ell F (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g))-
      ActualShiftedQuadraticWardPayment.liveResponseCorrection m ell F (causalFrequency advanced sourceMu ω)
        (causal_nonreal advanced sourceMu mu_positive ω) g)=causalCorrected advanced m ell F g:=by
    funext ω
    rw [ActualShiftedQuadraticWardPayment.actual_live_response_parts,
      ActualNativeOwnSquareWardPayment.actual_native_own_flux_source]
    unfold causalCorrected causalNative causalRadial ActualUnweightedSquareCurrentPayment.shiftedResponse
    rw [hB]
    simp only [coreWindow,Module.End.mul_apply]
    rw [unweighted_core_return]
    ring
  rw [hfun] at hf
  exact hf

elab "paid_bpr_native%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualNativeInvoiceSourceReturn 0) "LowEnergy")
    "ActualNativeInvoiceSourceReturn") field.getId.eraseMacroScopes.toString)
private theorem coefficient_nonnegative(sharp:Bool):0 ≤ rawCoefficient sharp:=by
  unfold rawCoefficient
  exact (paid_bpr_native% beta_nonnegative) sharp
private theorem causal_native_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (causalNative advanced m ell F g):=by
  apply (ActualBalancedPressureFrequencyPayment.actual_native_own_flux_integrable advanced m ell F g).congr
  apply Eventually.of_forall
  intro ω
  unfold causalNative
  exact (paid_bpr_native% flux_congr) m ell F _ _ _ _ g
    ((paid_bpr_native% causal_actual) advanced sourceMu ω).symm
private theorem causal_radial_lower(advanced:Bool)(m ell:ℕ)(hm:1 ≤ m)(hml:m ≤ ell)
    (F:Index)(g:QuantumTest):
    -(432*phaseCoefficient/3481)*((∫ω:ℝ,inverseForm (thetaAction (m/2) m
        (resolventCore F (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g)))+
      (∫ω:ℝ,inverseForm (thetaAction (ell/2) ell
        (resolventCore F (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g)))) ≤
      ∫ω:ℝ,(causalRadial advanced m ell F g ω).re:=by
  have hp:=(paid_bpr_native% radial_integral_lower) advanced m ell hm hml F g
  have hf:(fun ω:ℝ=>(causalRadial advanced m ell F g ω).re)=
      (fun ω:ℝ=>((paid_bpr_native% radialFrequency) advanced m ell F g ω).re):=by
    funext ω
    unfold causalRadial
    apply congrArg Complex.re
    exact (paid_bpr_native% radial_congr) m ell F _ _ _ _ g
      ((paid_bpr_native% causal_actual) advanced sourceMu ω)
  rw [hf]
  have hq(ω:ℝ):resolventCore F (causalFrequency advanced sourceMu ω)
      (causal_nonreal advanced sourceMu mu_positive ω) g=(paid_bpr_native% q) advanced F g ω:=by
    exact LinearMap.congr_fun ((paid_bpr_native% resolvent_congr) F _ _ _ _
      ((paid_bpr_native% causal_actual) advanced sourceMu ω)) g
  simp_rw [hq]
  exact hp

attribute [local irreducible] ActualTwoResolventSylvester.sourceL SourceEscapeSeedTail.actualIncrement
  sourceQ ActualExactSylvesterRawFrequencyBalance.rawFrequencyResidual
  ActualBulkCurrentSquareReturn.forceResponse reserveFrequency
  ActualNativeOwnSquareWardPayment.nativeOwnFlux

private theorem original_raw_paid_return(g:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀ advanced sharp:Bool,
      (∫ω:ℝ,ActualExactSylvesterRawFrequencyBalance.rawFrequencyResidual advanced sharp m ell F g ω)-
        rawCoefficient sharp*(∫ω:ℝ,(ActualUnweightedSquareCurrentPayment.shiftedResponse advanced m ell F g ω).re) ≥
      Real.pi*sourceQ sharp m ell g+(2/sourceMu)*(∫ω:ℝ,reserveFrequency advanced sharp m ell F g ω)+
      2*Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu
        (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)‖^2+
      (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*
        (∫ω:ℝ,ActualBulkCurrentSquareReturn.forceResponse advanced m ell F g ω)-ε:=by
  simpa only [rawCoefficient] using
    ActualUnweightedSquareCurrentPayment.actual_raw_shifted_square_paid_return g

private theorem scalar_terminal{raw shift native invoice work reserve force boundary boundaryL radial corr corrAbs win winAbs
    b debt ε δ:ℝ}(hε:0 < ε)
    (h0:raw-b*shift ≥ boundary+reserve+boundaryL+force-ε/4)
    (hNative:b*native ≥ b*(invoice-δ))
    (hRadial:-debt ≤ b*radial)
    (hSmall:b*δ ≤ ε/4)
    (hCorr:b*corrAbs ≤ b*δ)
    (hWin:b*winAbs ≤ b*δ)
    (hLower:b*(-corrAbs) ≤ b*corr)
    (hEq:corr=shift-native-radial)
    (hUpper:b*win ≤ b*winAbs)
    (hWork:work=b*invoice+(3/4:ℝ)*reserve+force+(b/12)*win):
    raw ≥ boundary+(1/4:ℝ)*reserve+boundaryL+work-debt-ε:=by
  have he:=congrArg (fun x:ℝ=>b*x) hEq
  nlinarith only [hε,h0,hNative,hRadial,hSmall,hCorr,hWin,hLower,he,hUpper,hWork]

/-- One original raw balance pays the whole moving source current. The
retained-joint branch is independent; no reserve is credited twice here. -/
theorem actual_raw_pressure_reserve_return(g:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced sharp:Bool,
      Integrable (clearedNativeWork advanced sharp m ell F g) ∧
      (∫ω:ℝ,ActualExactSylvesterRawFrequencyBalance.rawFrequencyResidual advanced sharp m ell F g ω) ≥
        Real.pi*sourceQ sharp m ell g+(1/4:ℝ)*(2/sourceMu)*
          (∫ω:ℝ,reserveFrequency advanced sharp m ell F g ω)+
        2*Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu
          (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)‖^2+
        (∫ω:ℝ,clearedNativeWork advanced sharp m ell F g ω)-
        rawCoefficient sharp*(432*phaseCoefficient/3481)*
          ((∫ω:ℝ,inverseForm (thetaAction (m/2) m
            (resolventCore F (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g)))+
          (∫ω:ℝ,inverseForm (thetaAction (ell/2) ell
            (resolventCore F (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g))))-ε:=by
  intro ε hε
  let B:=rawCoefficient false+rawCoefficient true
  have hB:0 ≤ B:=add_nonneg (coefficient_nonnegative false) (coefficient_nonnegative true)
  let δ:=(ε/4)/(B+1)
  have hδ:0 < δ:=div_pos (by positivity) (by linarith only [hB])
  obtain ⟨N0,h0⟩:=original_raw_paid_return g (ε/4) (by positivity)
  obtain ⟨N1,h1⟩:=ActualPressureProductCrossPayment.actual_source_moving_current_native_lower g δ hδ
  obtain ⟨N2,h2⟩:=causal_corrected_tail g δ hδ
  obtain ⟨N3,h3⟩:=fixed_pressure_window_tail sourceMu mu_positive g δ hδ
  refine ⟨max 1 (max N0 (max N1 (max N2 N3))),fun m hm ell hml=>?_⟩
  filter_upwards [h0 m (by omega) ell hml,h1 m (by omega) ell hml,
    h2 m (by omega) ell hml,h3 m (by omega) ell hml] with F hF0 hF1 hF2 hF3
  intro advanced sharp
  have hp0:=hF0 advanced sharp
  obtain ⟨hInvoice,hNative⟩:=hF1 advanced
  have hPair:Integrable (causalCorrected advanced m ell F g) ∧
      ‖∫ω:ℝ,causalCorrected advanced m ell F g ω‖ ≤ δ:=hF2 advanced
  have hCorrected:=hPair.1
  have hCorrectedSmall:=hPair.2
  have hWP:Integrable (fixedPressureWindow advanced sourceMu mu_positive m ell F g) ∧
      ‖∫ω:ℝ,fixedPressureWindow advanced sourceMu mu_positive m ell F g ω‖ ≤ δ:=hF3 advanced
  have hWindow:=hWP.1
  have hWindowSmall:=hWP.2
  have hReserve:Integrable (reserveFrequency advanced sharp m ell F g):=
    (paid_bpr_raw% reserve_frequency_integrable) advanced sharp m ell F g
  have hForce:Integrable (ActualBulkCurrentSquareReturn.forceResponse advanced m ell F g):=
    (paid_bpr_force% force_response_integrable) advanced m ell F g
  have hWinRe:Integrable (fun ω:ℝ=>(fixedPressureWindow advanced sourceMu mu_positive m ell F g ω).re):=by
    simpa only [RCLike.re_to_complex] using hWindow.re
  have hWork:Integrable (clearedNativeWork advanced sharp m ell F g):=by
    apply ((((hInvoice.const_mul (rawCoefficient sharp)).add
      (hReserve.const_mul ((3/4:ℝ)*(2/sourceMu)))).add
      (hForce.const_mul (24*bulkCoefficient sharp*sourceMu/phaseCoefficient))).add
      (hWinRe.const_mul (rawCoefficient sharp/12))).congr
    apply Eventually.of_forall
    intro ω
    simp only [Pi.add_apply]
    exact (cleared_native_work_return advanced sharp m ell F g ω).symm
  have hWorkIntegral:(∫ω:ℝ,clearedNativeWork advanced sharp m ell F g ω)=
      rawCoefficient sharp*(∫ω:ℝ,ActualPressureProductCrossPayment.movingCurrentInvoice
        advanced sourceMu mu_positive m ell F g ω)+
      (3/4:ℝ)*(2/sourceMu)*(∫ω:ℝ,reserveFrequency advanced sharp m ell F g ω)+
      (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*
        (∫ω:ℝ,ActualBulkCurrentSquareReturn.forceResponse advanced m ell F g ω)+
      (rawCoefficient sharp/12)*(∫ω:ℝ,(fixedPressureWindow advanced sourceMu mu_positive m ell F g ω).re):=by
    have hfun:=funext (cleared_native_work_return advanced sharp m ell F g)
    rw [hfun]
    have hS1:=(hInvoice.const_mul (rawCoefficient sharp)).add (hReserve.const_mul ((3/4:ℝ)*(2/sourceMu)))
    have hS2:=hS1.add (hForce.const_mul (24*bulkCoefficient sharp*sourceMu/phaseCoefficient))
    have he:=integral_add hS2 (hWinRe.const_mul (rawCoefficient sharp/12))
    simp only [Pi.add_apply] at he
    rw [he,integral_const_mul]
    have he2:=integral_add hS1 (hForce.const_mul (24*bulkCoefficient sharp*sourceMu/phaseCoefficient))
    simp only [Pi.add_apply] at he2
    rw [he2,integral_const_mul]
    have he1:=integral_add (hInvoice.const_mul (rawCoefficient sharp))
      (hReserve.const_mul ((3/4:ℝ)*(2/sourceMu)))
    rw [he1,integral_const_mul,integral_const_mul]
  have hFlux:=causal_native_integrable advanced m ell F g
  have hShift:=ActualUnweightedSquareCurrentPayment.actual_shifted_response_integrable advanced m ell F g
  have hRadial:Integrable (causalRadial advanced m ell F g):=by
    apply ((hShift.sub hFlux).sub hCorrected).congr
    apply Eventually.of_forall
    intro ω
    unfold causalCorrected
    simp only [Pi.sub_apply]
    ring
  have hCorrEq:(∫ω:ℝ,(causalCorrected advanced m ell F g ω).re)=
      (∫ω:ℝ,(ActualUnweightedSquareCurrentPayment.shiftedResponse advanced m ell F g ω).re)-
      (∫ω:ℝ,(causalNative advanced m ell F g ω).re)-(∫ω:ℝ,(causalRadial advanced m ell F g ω).re):=by
    have hs:Integrable (fun ω:ℝ=>(ActualUnweightedSquareCurrentPayment.shiftedResponse advanced m ell F g ω).re):=by
      simpa only [RCLike.re_to_complex] using hShift.re
    have hn:Integrable (fun ω:ℝ=>(causalNative advanced m ell F g ω).re):=by
      simpa only [RCLike.re_to_complex] using hFlux.re
    have hr:Integrable (fun ω:ℝ=>(causalRadial advanced m ell F g ω).re):=by
      simpa only [RCLike.re_to_complex] using hRadial.re
    simp only [causalCorrected,Complex.sub_re]
    have he:=integral_sub (hs.sub hn) hr
    simp only [Pi.sub_apply] at he
    rw [he,integral_sub hs hn]
  have bound{v:ℝ→ℂ}(hi:Integrable v)(hv:‖∫ω:ℝ,v ω‖ ≤ δ):
      |∫ω:ℝ,(v ω).re| ≤ δ:=by
    have he:=integral_re hi
    simp only [RCLike.re_to_complex] at he
    rw [he]
    exact (Complex.abs_re_le_norm _).trans hv
  have hb:=coefficient_nonnegative sharp
  have hsharp:rawCoefficient sharp ≤ B:=by
    cases sharp
    · exact le_add_of_nonneg_right (coefficient_nonnegative true)
    · exact le_add_of_nonneg_left (coefficient_nonnegative false)
  have hSmall:rawCoefficient sharp*δ ≤ ε/4:=by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith only [hB] : 0 < B+1)).mpr
    nlinarith only [hsharp,hε]
  have hcBound:=bound hCorrected hCorrectedSmall
  have hwBound:=bound hWindow hWindowSmall
  have hcError:=mul_le_mul_of_nonneg_left hcBound hb
  have hwError:=mul_le_mul_of_nonneg_left hwBound hb
  have hcLower:=mul_le_mul_of_nonneg_left (neg_abs_le (∫ω:ℝ,(causalCorrected advanced m ell F g ω).re)) hb
  have hwUpper:=mul_le_mul_of_nonneg_left (le_abs_self (∫ω:ℝ,(fixedPressureWindow advanced sourceMu mu_positive m ell F g ω).re)) hb
  have hNP:(∫ω:ℝ,(causalNative advanced m ell F g ω).re) ≥
      (∫ω:ℝ,ActualPressureProductCrossPayment.movingCurrentInvoice advanced sourceMu mu_positive m ell F g ω)-δ:=by
    simpa only [causalNative] using hNative
  have hNativePaid:=mul_le_mul_of_nonneg_left hNP hb
  have hRadPaid:=mul_le_mul_of_nonneg_left (causal_radial_lower advanced m ell (by omega) hml F g) hb
  refine ⟨hWork,?_⟩
  let debt:=rawCoefficient sharp*(432*phaseCoefficient/3481)*
    ((∫ω:ℝ,inverseForm (thetaAction (m/2) m
      (resolventCore F (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g)))+
    (∫ω:ℝ,inverseForm (thetaAction (ell/2) ell
      (resolventCore F (causalFrequency advanced sourceMu ω) (causal_nonreal advanced sourceMu mu_positive ω) g))))
  have hRP:-debt ≤ rawCoefficient sharp*(∫ω:ℝ,(causalRadial advanced m ell F g ω).re):=by
    dsimp only [debt]
    convert hRadPaid using 1 <;> first | rfl | ring
  have hWP:(∫ω:ℝ,clearedNativeWork advanced sharp m ell F g ω)=
      rawCoefficient sharp*(∫ω:ℝ,ActualPressureProductCrossPayment.movingCurrentInvoice
        advanced sourceMu mu_positive m ell F g ω)+
      (3/4:ℝ)*((2/sourceMu)*(∫ω:ℝ,reserveFrequency advanced sharp m ell F g ω))+
      (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*
        (∫ω:ℝ,ActualBulkCurrentSquareReturn.forceResponse advanced m ell F g ω)+
      (rawCoefficient sharp/12)*(∫ω:ℝ,(fixedPressureWindow advanced sourceMu mu_positive m ell F g ω).re):=by
    convert hWorkIntegral using 1
    first | rfl | ring
  have hResult:=scalar_terminal hε hp0 hNativePaid hRP hSmall hcError hwError hcLower hCorrEq hwUpper hWP
  dsimp only [debt] at hResult
  convert hResult using 1
  first | rfl | ring

end LowEnergy.ActualBalancedPressureRadialPayment
