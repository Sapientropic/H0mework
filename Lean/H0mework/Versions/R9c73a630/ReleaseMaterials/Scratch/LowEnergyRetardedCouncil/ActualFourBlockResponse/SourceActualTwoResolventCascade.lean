import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventStorage
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCascadeBlockAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualTwoResolventCascade
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory SourceQuantumScalarChart
open SourceMixedNativeReturn SourceScalarInverseNativeEnergy SourceScalarInverseEnergyBudget
open SourceInverseFixedEnergyTail SourceHardyRetardedTail SourceRelativePowerTail
open SourceCutoffDilationWard SourceRetardedGraph
open scoped InnerProductSpace Matrix
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev theta := SourceNativeCutoffContact.thetaAction
private theorem mu_pos : 0<sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large

open SourceScalarPairedTransport SourceScalarDoubleCurrent SourceInverseNoetherEnergy

/-- The bulk action remains a core form. It is not asserted to extend boundedly
on H. This is the actual source Q in the paired two-core storage. -/
def sourceQAction (sharp:Bool) (m ell:ℕ) : End :=
  (bulkCoefficient sharp:ℂ) • (theta m ell*bulkAction*theta m ell)+
    (normCoefficient sharp:ℂ) • (theta m ell*theta m ell)
def sourceE (sharp:Bool) (m ell:ℕ) : End :=
  sourceL (!sharp) m ell*sourceL sharp m ell+sourceQAction sharp m ell

def causalSign (advanced:Bool) : ℝ := if advanced then -1 else 1
def sourceA (advanced:Bool) (F:Index) : End :=
  -(sourceMu:ℂ) • (1:End)-(Complex.I*(causalSign advanced:ℂ)) • compressionCore F
def sourceADual (advanced:Bool) (F:Index) : End :=
  -(sourceMu:ℂ) • (1:End)+(Complex.I*(causalSign advanced:ℂ)) • compressionCore F

def sourceCascade (advanced sharp:Bool) (m ell:ℕ) (F:Index) : Matrix (Fin 2) (Fin 2) End :=
  !![sourceA advanced F,literalIncrementAction sharp m ell;0,sourceA advanced F]
def sourceCascadeDual (advanced sharp:Bool) (m ell:ℕ) (F:Index) : Matrix (Fin 2) (Fin 2) End :=
  !![sourceADual advanced F,0;literalIncrementAction (!sharp) m ell,sourceADual advanced F]
def sourceP (sharp:Bool) (m ell:ℕ) : Matrix (Fin 2) (Fin 2) End :=
  !![1,sourceL sharp m ell;sourceL (!sharp) m ell,sourceE sharp m ell]
def sourceM (advanced sharp:Bool) (m ell:ℕ) (F:Index) : Matrix (Fin 2) (Fin 2) End :=
  -(sourceCascadeDual advanced sharp m ell F)*sourceP sharp m ell-
    sourceP sharp m ell*sourceCascade advanced sharp m ell F-!![1,0;0,0]

private theorem damping_left (C L:End) (s:ℂ) :
    -((-(sourceMu:ℂ) • (1:End)+s • C)*L)-
      L*(-(sourceMu:ℂ) • (1:End)-s • C)=
      (2*(sourceMu:ℂ)) • L-s • (C*L-L*C) := by
  simp only [add_mul,mul_sub,smul_mul_assoc,mul_smul_comm,
    one_mul,mul_one,smul_sub]
  module

private theorem sourceL_cancel (sharp:Bool) (m ell:ℕ) :
    (2*(sourceMu:ℂ)) • sourceL sharp m ell=literalIncrementAction sharp m ell := by
  unfold sourceL
  rw [smul_smul]
  have hm:(sourceMu:ℂ)≠0:=Complex.ofReal_ne_zero.mpr mu_pos.ne'
  have hc:(2*(sourceMu:ℂ))*((1/(2*sourceMu):ℝ):ℂ)=1 := by
    push_cast
    field_simp
  rw [hc,one_smul]

attribute [local irreducible] sourceL sourceE sourceQAction compressionCore literalIncrementAction

/-- All four actual source blocks are expanded together. The commutators retain
CF, not an H0 replacement, and no positivity premise is used. -/
theorem actual_source_blocks (advanced sharp:Bool) (m ell:ℕ) (F:Index) :
    sourceM advanced sharp m ell F=
      !![((2*sourceMu-1:ℝ):ℂ) • (1:End),
          -(Complex.I*(causalSign advanced:ℂ)) • bracket (compressionCore F) (sourceL sharp m ell);
        -(Complex.I*(causalSign advanced:ℂ)) • bracket (compressionCore F) (sourceL (!sharp) m ell),
          (2*(sourceMu:ℂ)) • sourceE sharp m ell-
            (Complex.I*(causalSign advanced:ℂ)) • bracket (compressionCore F) (sourceE sharp m ell)-
            literalIncrementAction (!sharp) m ell*sourceL sharp m ell-
            sourceL (!sharp) m ell*literalIncrementAction sharp m ell] := by
  unfold sourceM sourceCascadeDual sourceP sourceCascade
  rw [ActualCascadeBlockAlgebra.residual]
  apply ActualCascadeBlockAlgebra.four_congr
  · unfold sourceA sourceADual
    push_cast
    module
  · have h:=damping_left (compressionCore F) (sourceL sharp m ell)
      (Complex.I*(causalSign advanced:ℂ))
    rw [sourceL_cancel] at h
    change -sourceADual advanced F*sourceL sharp m ell-literalIncrementAction sharp m ell-
      sourceL sharp m ell*sourceA advanced F=_
    calc
      _=(-sourceADual advanced F*sourceL sharp m ell-
        sourceL sharp m ell*sourceA advanced F)-literalIncrementAction sharp m ell := by simp only [neg_mul]; abel
      _=(literalIncrementAction sharp m ell-
        (Complex.I*(causalSign advanced:ℂ)) • bracket (compressionCore F) (sourceL sharp m ell))-
        literalIncrementAction sharp m ell := by
          rw [neg_mul]
          exact congrArg (fun T:End=>T-literalIncrementAction sharp m ell) h
      _=_ := by module
  · have h:=damping_left (compressionCore F) (sourceL (!sharp) m ell)
      (Complex.I*(causalSign advanced:ℂ))
    rw [sourceL_cancel] at h
    calc
      _=(-sourceADual advanced F*sourceL (!sharp) m ell-
        sourceL (!sharp) m ell*sourceA advanced F)-literalIncrementAction (!sharp) m ell := by simp only [neg_mul]; abel
      _=(literalIncrementAction (!sharp) m ell-
        (Complex.I*(causalSign advanced:ℂ)) • bracket (compressionCore F) (sourceL (!sharp) m ell))-
        literalIncrementAction (!sharp) m ell := by
          rw [neg_mul]
          exact congrArg (fun T:End=>T-literalIncrementAction (!sharp) m ell) h
      _=_ := by module
  · have h:=damping_left (compressionCore F) (sourceE sharp m ell)
      (Complex.I*(causalSign advanced:ℂ))
    calc
      _=(-sourceADual advanced F*sourceE sharp m ell-sourceE sharp m ell*sourceA advanced F)-
        literalIncrementAction (!sharp) m ell*sourceL sharp m ell-
        sourceL (!sharp) m ell*literalIncrementAction sharp m ell := by simp only [neg_mul]; abel
      _=_ := by
        rw [neg_mul]
        exact congrArg (fun T:End=>T-literalIncrementAction (!sharp) m ell*sourceL sharp m ell-
          sourceL (!sharp) m ell*literalIncrementAction sharp m ell) h

/-- The full original own defect is the exact price of replacing CF by H0.
Neither moving core leg is treated as a fixed source jet. -/
theorem actual_compression_current (F:Index) (T:End) :
    bracket (compressionCore F) T=bracket diagonalAction T-defectAction F*T+T*defectAction F := by
  unfold bracket defectAction
  noncomm_ring
private theorem source_increment_adjoint (sharp:Bool) (m ell:ℕ) :
    (SourceEscapeSeedTail.actualIncrement sharp m ell).adjoint=
      SourceEscapeSeedTail.actualIncrement (!sharp) m ell := by
  cases sharp
  · change (FullYSourceCutoffVolterra.cutoff ell-FullYSourceCutoffVolterra.cutoff m).adjoint=
      (FullYSourceCutoffVolterra.cutoff ell).adjoint-(FullYSourceCutoffVolterra.cutoff m).adjoint
    exact map_sub _ _ _
  · change ((FullYSourceCutoffVolterra.cutoff ell).adjoint-(FullYSourceCutoffVolterra.cutoff m).adjoint).adjoint=
      FullYSourceCutoffVolterra.cutoff ell-FullYSourceCutoffVolterra.cutoff m
    rw [map_sub,ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.adjoint_adjoint]
private theorem increment_pair (sharp:Bool) (m ell:ℕ) (f g:QuantumTest) :
    sourcePair f (literalIncrementAction sharp m ell g)=
      sourcePair (literalIncrementAction (!sharp) m ell f) g := by
  simp only [sourcePair,←literal_increment_core]
  rw [←ContinuousLinearMap.adjoint_inner_left,source_increment_adjoint]
private theorem sourceL_pair (sharp:Bool) (m ell:ℕ) (f g:QuantumTest) :
    sourcePair f (sourceL sharp m ell g)=sourcePair (sourceL (!sharp) m ell f) g := by
  have hi:=increment_pair sharp m ell f g
  unfold sourceL
  simp only [sourcePair,LinearMap.smul_apply,map_smul,inner_smul_right,inner_smul_left,
    Complex.conj_ofReal] at hi ⊢
  rw [hi]
private theorem theta_pair (m ell:ℕ) (f g:QuantumTest) :
    sourcePair f (theta m ell g)=sourcePair (theta m ell f) g :=
  multiply_pair _ _ _ _
private theorem sourceQAction_energy (sharp:Bool) (m ell:ℕ) (f:QuantumTest) :
    (sourcePair f (sourceQAction sharp m ell f)).re=sourceQ sharp m ell f := by
  unfold sourceQAction sourceQ
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply]
  have hp (x y:QuantumTest)(a b:ℝ) :
      (sourcePair f ((a:ℂ) • x+(b:ℂ) • y)).re=
        a*(sourcePair f x).re+b*(sourcePair f y).re := by
    simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right,Complex.add_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hp,theta_pair,theta_pair,original_bulk_energy]
  change _+normCoefficient sharp*(inner ℂ (embed (theta m ell f)) (embed (theta m ell f))).re=_
  have hh:(inner ℂ (embed (theta m ell f)) (embed (theta m ell f))).re=
      ‖embed (theta m ell f)‖^2:=inner_self_eq_norm_sq (𝕜:=ℂ) _
  rw [hh]

theorem actual_sourceE_energy (sharp:Bool) (m ell:ℕ) (f:QuantumTest) :
    (sourcePair f (sourceE sharp m ell f)).re=initialStorage sharp m ell f := by
  unfold sourceE initialStorage
  simp only [LinearMap.add_apply,Module.End.mul_apply,sourcePair,map_add,inner_add_right,Complex.add_re]
  change (sourcePair f (sourceL (!sharp) m ell (sourceL sharp m ell f))).re+
    (sourcePair f (sourceQAction sharp m ell f)).re=_
  rw [sourceL_pair,Bool.not_not,sourceQAction_energy]
  exact congrArg (fun r:ℝ=>r+sourceQ sharp m ell f)
    (inner_self_eq_norm_sq (𝕜:=ℂ) (embed (sourceL sharp m ell f)))

/-- The completed square is the actual paired core P, not a supplied PSD field. -/
theorem actual_source_storage_square (sharp:Bool) (m ell:ℕ) (x y:QuantumTest) :
    (sourcePair x (x+sourceL sharp m ell y)+
      sourcePair y (sourceL (!sharp) m ell x+sourceE sharp m ell y)).re=
      ‖embed x+embed (sourceL sharp m ell y)‖^2+sourceQ sharp m ell y := by
  have hp:=sourceL_pair (!sharp) m ell y x
  rw [Bool.not_not] at hp
  simp only [sourcePair,map_add,inner_add_right,Complex.add_re]
  change (inner ℂ (embed x) (embed x)).re+(sourcePair x (sourceL sharp m ell y)).re+
    ((sourcePair y (sourceL (!sharp) m ell x)).re+(sourcePair y (sourceE sharp m ell y)).re)=_
  rw [hp,actual_sourceE_energy]
  unfold initialStorage
  have hx:(inner ℂ (embed x) (embed x)).re=‖embed x‖^2:=inner_self_eq_norm_sq (𝕜:=ℂ) _
  have hn:=norm_add_sq (𝕜:=ℂ) (embed x) (embed (sourceL sharp m ell y))
  change ‖embed x+embed (sourceL sharp m ell y)‖^2=
    ‖embed x‖^2+2*(sourcePair x (sourceL sharp m ell y)).re+‖embed (sourceL sharp m ell y)‖^2 at hn
  rw [hx,hn]
  have hs:=inner_re_symm (𝕜:=ℂ) (embed (sourceL sharp m ell y)) (embed x)
  change (sourcePair (sourceL sharp m ell y) x).re=(sourcePair x (sourceL sharp m ell y)).re at hs
  rw [hs]
  ring

theorem actual_source_storage_nonnegative (sharp:Bool) (m ell:ℕ) (x y:QuantumTest) :
    0 ≤ (sourcePair x (x+sourceL sharp m ell y)+
      sourcePair y (sourceL (!sharp) m ell x+sourceE sharp m ell y)).re := by
  rw [actual_source_storage_square]
  exact add_nonneg (sq_nonneg _) (actual_sourceQ_nonnegative sharp m ell y)
/-- The primitive source coefficients pay the whole diagonal damping debit.
The separate CF-current terms in actual_source_blocks remain present. -/
theorem actual_damping_price (sharp:Bool) (m ell:ℕ) (f:QuantumTest) :
    (2*sourceMu)*‖embed (theta m ell f)‖^2 ≤
      (2*sourceMu)*initialStorage sharp m ell f-
        ‖embed (literalIncrementAction sharp m ell f)‖^2/sourceMu := by
  have hp:=actual_primitive_storage_price sharp m ell f
  have hm:=mu_pos
  have he : ‖embed (literalIncrementAction sharp m ell f)‖^2=
      (4*sourceMu^2)*‖embed (sourceL sharp m ell f)‖^2 := by
    rw [actual_sourceL_norm,actual_increment_core]
    field_simp
  rw [he]
  have hc:(4*sourceMu^2)*‖embed (sourceL sharp m ell f)‖^2/sourceMu=
      (4*sourceMu)*‖embed (sourceL sharp m ell f)‖^2 := by
    field_simp
  rw [hc]
  unfold initialStorage
  nlinarith only [mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*sourceMu by positivity)]
private theorem compression_embed (F:Index) (f:QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_pair (F:Index) (f g:QuantumTest) :
    sourcePair f (compressionCore F g)=sourcePair (compressionCore F f) g := by
  simp only [sourcePair,compression_embed]
  exact ((GaussGradedCompression.compression_selfAdjoint F).isSymmetric _ _).symm
private theorem sourceA_pair (advanced:Bool) (F:Index) (f g:QuantumTest) :
    sourcePair f (sourceA advanced F g)=sourcePair (sourceADual advanced F f) g := by
  have hc:=compression_pair F f g
  unfold sourceA sourceADual
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
    sourcePair,map_sub,map_add,map_smul,inner_sub_right,inner_add_left,inner_smul_left,
    inner_smul_right,map_neg,map_mul,Complex.conj_ofReal,Complex.conj_I] at hc ⊢
  rw [hc]
  ring

/-- The lower triangular matrix is the formal source adjoint of the original
upper triangular cascade on the same paired core. -/
theorem actual_cascade_source_pair (advanced sharp:Bool) (m ell:ℕ) (F:Index)
    (x0 x1 y0 y1:QuantumTest) :
    sourcePair x0 (sourceA advanced F y0+literalIncrementAction sharp m ell y1)+
      sourcePair x1 (sourceA advanced F y1)=
    sourcePair (sourceADual advanced F x0) y0+
      sourcePair (literalIncrementAction (!sharp) m ell x0+sourceADual advanced F x1) y1 := by
  have ha:=sourceA_pair advanced F x0 y0
  have hb:=sourceA_pair advanced F x1 y1
  have hd:=increment_pair sharp m ell x0 y1
  simp only [sourcePair,map_add,inner_add_right,inner_add_left] at ha hb hd ⊢
  rw [ha,hb,hd]
  ring

end LowEnergy.ActualTwoResolventCascade
