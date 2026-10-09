import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseBulkSquare
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardFrequencyReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardMomentTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualScalarPhaseFrequencyReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy GaussNativeForm GaussCoframeForm SourceScalarShiftedBulk SourcePhysicalKineticSquare
open SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceNativeCutoffContact
open ActualScalarPhaseJet ActualMixedCompressionShape ActualMixedCovarianceTail ActualMixedWindowGram
open ActualWeightedWardInputSplit ActualMixedWardFrequencyReturn ActualSylvesterCore ActualSylvesterChannels
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceResolventBandLimit FullYSourceResolventGraphSplice
open ActualVectorJointCost MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators ENNReal
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore resolventCore phaseGenerator diagonalAction sourcePair

elab "paid_phase_inverse%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedResolventWard 0) "LowEnergy") "ActualMixedResolventWard"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing original inverse proof"
  mkConstWithFreshMVarLevels name
elab "paid_phase_frequency%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardFrequencyReturn 0) "LowEnergy") "ActualMixedWardFrequencyReturn"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing original frequency proof"
  mkConstWithFreshMVarLevels name
elab "paid_phase_moment%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardMomentTail 0) "LowEnergy") "ActualMixedWardMomentTail"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing original fixed-source moment proof"
  mkConstWithFreshMVarLevels name
elab "paid_phase_pair%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovarianceGram 0) "LowEnergy") "ActualMixedCovarianceGram"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing original paired source proof"
  mkConstWithFreshMVarLevels name

private theorem phase_mul(A B:End):phaseJet (A*B)=phaseJet A*B+A*phaseJet B := by
  simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk]
  noncomm_ring
private theorem phase_one:phaseJet (1:End)=0 := by
  simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk,mul_one,one_mul,sub_self]
private theorem phase_zero:phaseJet (0:End)=0 := by
  simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk,mul_zero,zero_mul,sub_self]
private theorem phase_second_one:phaseSecond (1:End)=0 := by
  change phaseJet (phaseJet (1:End))=0
  rw [phase_one,phase_zero]
private theorem theta_phase_zero(m ell:ℕ):phaseJet (thetaAction m ell)=0 := by
  have ht:Commute (thetaAction m ell) offsetAction:=(paid_offset_phase% real_offset) _ _
  simp only [phaseJet,phaseGenerator,LinearMap.coe_mk,AddHom.coe_mk,smul_mul_assoc,mul_smul_comm,ht.eq,sub_self]
private theorem theta_phase_commute(m ell:ℕ):phaseGenerator*thetaAction m ell=thetaAction m ell*phaseGenerator :=
  sub_eq_zero.mp (theta_phase_zero m ell)
private theorem pair_neg_right(f h:QuantumTest):sourcePair f (-h)= -sourcePair f h := by
  simp only [sourcePair,map_neg,inner_neg_right]

private theorem phase_skew(f h:QuantumTest):
    sourcePair f (phaseGenerator h)= -sourcePair (phaseGenerator f) h := by
  simp only [phaseGenerator,LinearMap.smul_apply,sourcePair,map_smul,inner_smul_left,inner_smul_right,
    Complex.conj_I,neg_mul,neg_neg]
  have hp:=(paid_offset_phase% offset_pair) f h
  simp only [sourcePair] at hp
  exact congrArg (Complex.I*·) hp
private theorem phase_apply(A:End)(f:QuantumTest):
    phaseJet A f=phaseGenerator (A f)-A (phaseGenerator f) := rfl
private theorem phase_second_apply(A:End)(f:QuantumTest):
    phaseSecond A f=phaseGenerator (phaseGenerator (A f))-
      (2:ℂ) • phaseGenerator (A (phaseGenerator f))+A (phaseGenerator (phaseGenerator f)) := by
  change phaseJet (phaseJet A) f=_
  simp only [phase_apply,map_sub]
  module

theorem actual_phase_first_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    phaseJet (resolventCore F z hz)=
      -resolventCore F z hz*phaseJet (compressionCore F)*resolventCore F z hz := by
  have hi:=(paid_phase_inverse% actual_inverse) F z hz
  have h:=(paid_phase_inverse% inverse_comm) (compressionCore F-z • (1:End))
    (resolventCore F z hz) phaseGenerator hi.1 hi.2
  have he:phaseGenerator*(compressionCore F-z • (1:End))-
      (compressionCore F-z • (1:End))*phaseGenerator=phaseJet (compressionCore F) := by
    simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
    module
  change phaseGenerator*resolventCore F z hz-resolventCore F z hz*phaseGenerator=
    -resolventCore F z hz*(phaseGenerator*(compressionCore F-z • (1:End))-
      (compressionCore F-z • (1:End))*phaseGenerator)*resolventCore F z hz at h
  rw [he] at h
  exact h

/-- The same actual inverse differentiates twice, retaining both ordered first jets. -/
theorem actual_phase_second_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    phaseSecond (resolventCore F z hz)=
      (2:ℂ) • (resolventCore F z hz*phaseJet (compressionCore F)*resolventCore F z hz*
        phaseJet (compressionCore F)*resolventCore F z hz)-
      resolventCore F z hz*phaseSecond (compressionCore F)*resolventCore F z hz := by
  change phaseJet (phaseJet (resolventCore F z hz))=_
  rw [actual_phase_first_inverse]
  simp only [map_neg,phase_mul,actual_phase_first_inverse,phaseSecond,LinearMap.comp_apply,
    two_smul,neg_mul,mul_neg]
  noncomm_ring

/-- U, the original full first force, and the entire OwnDefect share one actual return. -/
theorem actual_source_U_phase_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    (phaseCoefficient:ℂ) • (resolventCore F z hz*inverseVolumeAction*resolventCore F z hz)=
      phaseSecond (resolventCore F z hz)-
      (2:ℂ) • (resolventCore F z hz*phaseJet (compressionCore F)*resolventCore F z hz*
        phaseJet (compressionCore F)*resolventCore F z hz)-
      resolventCore F z hz*phaseSecond (defectAction F)*resolventCore F z hz := by
  have hC:phaseSecond (compressionCore F)=
      -(phaseCoefficient:ℂ) • inverseVolumeAction-phaseSecond (defectAction F) := by
    have he:phaseSecond diagonalAction=-(phaseCoefficient:ℂ) • inverseVolumeAction := by
      simpa only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using actual_source_inverse_volume_phase_jet
    unfold defectAction
    rw [map_sub,he]
    module
  rw [actual_phase_second_inverse,hC]
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,neg_smul,mul_neg,neg_mul]
  module

theorem actual_source_U_raw_phase_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    (phaseCoefficient:ℂ) • (resolventCore F z hz*coreCompression F inverseVolumeAction*resolventCore F z hz)=
      phaseSecond (resolventCore F z hz)-
      (2:ℂ) • (resolventCore F z hz*phaseJet (compressionCore F)*resolventCore F z hz*
        phaseJet (compressionCore F)*resolventCore F z hz)+
      resolventCore F z hz*wholePhaseShape F*resolventCore F z hz := by
  rw [actual_phase_second_inverse,actual_source_inverse_volume_compression_phase]
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,neg_smul,mul_neg,neg_mul]
  simp only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow]
  module

private theorem resolvent_return(F:Index)(z:ℂ)(hz:z.im≠0):
    resolventCore F z hz*compressionCore F=1+z • resolventCore F z hz :=
  (paid_phase_frequency% resolvent_right) F z hz

theorem actual_phase_right_frequency(F:Index)(z:ℂ)(hz:z.im≠0):
    z • phaseJet (resolventCore F z hz)=
      phaseJet (resolventCore F z hz)*compressionCore F+
        resolventCore F z hz*phaseJet (compressionCore F) := by
  have h:=congrArg phaseJet (resolvent_return F z hz)
  rw [phase_mul,map_add,map_smul,phase_one,zero_add] at h
  exact h.symm

theorem actual_phase_right_second_frequency(F:Index)(z:ℂ)(hz:z.im≠0):
    z • phaseSecond (resolventCore F z hz)=
      phaseSecond (resolventCore F z hz)*compressionCore F+
        resolventCore F z hz*phaseSecond (compressionCore F)+
        (2:ℂ) • (phaseJet (resolventCore F z hz)*phaseJet (compressionCore F)) := by
  have h:=congrArg phaseSecond (resolvent_return F z hz)
  rw [actual_phase_second_product,map_add,map_smul,phase_second_one,zero_add] at h
  exact h.symm

private theorem resolvent_square_return(F:Index)(z:ℂ)(hz:z.im≠0):
    resolventCore F z hz*(compressionCore F*compressionCore F)=
      compressionCore F+z • (1:End)+(z^2) • resolventCore F z hz := by
  calc
    _=(1+z • resolventCore F z hz)*compressionCore F := by
      rw [←resolvent_return F z hz]
      noncomm_ring
    _=compressionCore F+z • (1+z • resolventCore F z hz) := by
      rw [add_mul,one_mul,smul_mul_assoc,resolvent_return]
    _=_ := by simp only [smul_add,smul_smul,pow_two];module

/-- The actual second inverse has one source-square forcing and one contact return. -/
theorem actual_phase_square_frequency(F:Index)(z:ℂ)(hz:z.im≠0):
    (z^2) • phaseSecond (resolventCore F z hz)=
      phaseSecond (resolventCore F z hz)*(compressionCore F*compressionCore F)+
        resolventCore F z hz*phaseSecond (compressionCore F*compressionCore F)+
        (2:ℂ) • (phaseJet (resolventCore F z hz)*phaseJet (compressionCore F*compressionCore F))-
        phaseSecond (compressionCore F) := by
  have h:=congrArg phaseSecond (resolvent_square_return F z hz)
  rw [actual_phase_second_product,map_add,map_add,map_smul,map_smul,
    phase_second_one,smul_zero,add_zero] at h
  linear_combination (norm:=module) -h

theorem actual_phase_first_square_frequency(F:Index)(z:ℂ)(hz:z.im≠0):
    (z^2) • phaseJet (resolventCore F z hz)=
      phaseJet (resolventCore F z hz)*(compressionCore F*compressionCore F)+
        resolventCore F z hz*phaseJet (compressionCore F*compressionCore F)-phaseJet (compressionCore F) := by
  have h:=congrArg phaseJet (resolvent_square_return F z hz)
  rw [phase_mul,map_add,map_add,map_smul,map_smul,phase_one,smul_zero,add_zero] at h
  linear_combination (norm:=module) -h

attribute [local irreducible] phaseJet phaseSecond

/-- The complete H0-square OwnDefect is retained before any fixed-source read. -/
def phaseSquareOwn(F:Index):End := diagonalAction*diagonalAction-compressionCore F*compressionCore F

theorem actual_phase_square_own_frequency(F:Index)(z:ℂ)(hz:z.im≠0):
    (z^2) • phaseSecond (resolventCore F z hz)=
      phaseSecond (resolventCore F z hz)*(compressionCore F*compressionCore F)+
        resolventCore F z hz*phaseSecond (diagonalAction*diagonalAction)-
        resolventCore F z hz*phaseSecond (phaseSquareOwn F)+
        (2:ℂ) • (phaseJet (resolventCore F z hz)*phaseJet (compressionCore F*compressionCore F))-
        phaseSecond (compressionCore F) := by
  have h:phaseSecond (compressionCore F*compressionCore F)=
      phaseSecond (diagonalAction*diagonalAction)-phaseSecond (phaseSquareOwn F) := by
    unfold phaseSquareOwn
    rw [map_sub]
    module
  rw [actual_phase_square_frequency,h]
  simp only [mul_sub]
  module

theorem actual_phase_square_own_shape(F:Index):
    phaseSecond (phaseSquareOwn F)=
      phaseSecond (defectAction F)*diagonalAction+
      defectAction F*phaseSecond diagonalAction+
      (2:ℂ) • (phaseJet (defectAction F)*phaseJet diagonalAction)+
      phaseSecond (compressionCore F)*defectAction F+
      compressionCore F*phaseSecond (defectAction F)+
      (2:ℂ) • (phaseJet (compressionCore F)*phaseJet (defectAction F)) := by
  have hs:phaseSquareOwn F=defectAction F*diagonalAction+compressionCore F*defectAction F := by
    unfold phaseSquareOwn defectAction
    noncomm_ring
  rw [hs,map_add,actual_phase_second_product,actual_phase_second_product]
  module

/-- Raw P, both actual projection derivatives, and every ordered cross survive squaring. -/
theorem actual_source_phase_square_own_shape(F:Index):
    phaseSecond (phaseSquareOwn F)=
      (-(phaseCoefficient:ℂ) • (inverseVolumeAction-coreCompression F inverseVolumeAction)-wholePhaseShape F)*diagonalAction+
      defectAction F*(-(phaseCoefficient:ℂ) • inverseVolumeAction)+
      (2:ℂ) • (phaseJet (defectAction F)*phaseJet diagonalAction)+
      phaseSecond (compressionCore F)*defectAction F+
      compressionCore F*(-(phaseCoefficient:ℂ) • (inverseVolumeAction-coreCompression F inverseVolumeAction)-wholePhaseShape F)+
      (2:ℂ) • (phaseJet (compressionCore F)*phaseJet (defectAction F)) := by
  rw [actual_phase_square_own_shape,actual_source_inverse_volume_own_phase,
    actual_source_inverse_volume_phase_jet]
  simp only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul]

def phasePair(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let W:=coreWindow m ell F z hz
  (2:ℂ)*sourcePair (thetaAction m ell (phaseJet R g)) (thetaAction m ell (phaseJet R h))+
    sourcePair (W g) (thetaAction m ell (phaseSecond R h))+
    sourcePair (thetaAction m ell (phaseSecond R g)) (W h)

attribute [local irreducible] phasePair coreWindow
attribute [local irreducible] SourceScalarInverseBulk.inverseSymmetricScale ActualPhaseBulkSquare.phaseForce

private theorem phase_pair_comm_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest):
    let R:=resolventCore F z hz
    let W:=thetaAction m ell*R
    let X:=thetaAction m ell*phaseJet R;
    sourcePair (X g) (W h)+sourcePair (W g) (X h)=
      -sourcePair (W (phaseGenerator g)) (W h)-sourcePair (W g) (W (phaseGenerator h)) := by
  dsimp only
  have he:thetaAction m ell*phaseJet (resolventCore F z hz)=
      phaseGenerator*(thetaAction m ell*resolventCore F z hz)-
        (thetaAction m ell*resolventCore F z hz)*phaseGenerator := by
    simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk]
    have ht:=congrArg (fun A:End=>A*resolventCore F z hz) (theta_phase_commute m ell)
    linear_combination (norm:=noncomm_ring) -ht
  rw [he]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right] at *
  have hp:=phase_skew (thetaAction m ell (resolventCore F z hz g))
    (thetaAction m ell (resolventCore F z hz h))
  simp only [sourcePair] at hp
  rw [hp]
  ring

/-- A true complex frequency return; no conjugate z or discarded derivative slot is used. -/
theorem actual_phase_whole_frequency_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let R:=resolventCore F z hz
    let C:=compressionCore F
    let W:=thetaAction m ell*R
    z*phasePair m ell F z hz g g=
      phasePair m ell F z hz g (C g)+sourcePair (W g) (W (phaseSecond C g))-
        (2:ℂ)*sourcePair (W (phaseGenerator g)) (W (phaseJet C g))-
        (2:ℂ)*sourcePair (W g) (W (phaseGenerator (phaseJet C g)))-
        sourcePair (thetaAction m ell (phaseSecond R g)) (thetaAction m ell g) := by
  dsimp only
  let R:=resolventCore F z hz
  let C:=compressionCore F
  let W:=thetaAction m ell*R
  let X:=thetaAction m ell*phaseJet R
  let S:=thetaAction m ell*phaseSecond R
  have hw(q:QuantumTest):z • W q=W (C q)-thetaAction m ell q := by
    have h:=congrArg (fun T:End=>thetaAction m ell (T q)) (resolvent_return F z hz)
    simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,map_add,map_smul] at h
    change W (C q)=thetaAction m ell q+z • W q at h
    rw [h]
    module
  have hx(q:QuantumTest):z • X q=X (C q)+W (phaseJet C q) := by
    have h:=congrArg (fun T:End=>thetaAction m ell (T q)) (actual_phase_right_frequency F z hz)
    simpa only [X,W,R,C,LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,map_smul,map_add] using h
  have hs(q:QuantumTest):z • S q=S (C q)+W (phaseSecond C q)+(2:ℂ) • X (phaseJet C q) := by
    have h:=congrArg (fun T:End=>thetaAction m ell (T q)) (actual_phase_right_second_frequency F z hz)
    simpa only [S,X,W,R,C,LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,map_smul,map_add] using h
  have hf:z*phasePair m ell F z hz g g=
      phasePair m ell F z hz g (C g)+sourcePair (W g) (W (phaseSecond C g))+
        (2:ℂ)*sourcePair (X g) (W (phaseJet C g))+
        (2:ℂ)*sourcePair (W g) (X (phaseJet C g))-sourcePair (S g) (thetaAction m ell g) := by
    simp only [phasePair,coreWindow,Module.End.mul_apply]
    change z*((2:ℂ)*sourcePair (X g) (X g)+sourcePair (W g) (S g)+sourcePair (S g) (W g))=
      ((2:ℂ)*sourcePair (X g) (X (C g))+sourcePair (W g) (S (C g))+sourcePair (S g) (W (C g)))+
        sourcePair (W g) (W (phaseSecond C g))+(2:ℂ)*sourcePair (X g) (W (phaseJet C g))+
        (2:ℂ)*sourcePair (W g) (X (phaseJet C g))-sourcePair (S g) (thetaAction m ell g)
    calc
      _=(2:ℂ)*sourcePair (X g) (z • X g)+sourcePair (W g) (z • S g)+sourcePair (S g) (z • W g) := by
        simp only [(paid_phase_frequency% pair_smul_right)]
        ring
      _=_ := by
        rw [hx,hs,hw]
        simp only [(paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_sub_right),
          (paid_phase_frequency% pair_smul_right)]
        ring
  have hr:=phase_pair_comm_return m ell F z hz g (phaseJet C g)
  dsimp only at hr
  change sourcePair (X g) (W (phaseJet C g))+sourcePair (W g) (X (phaseJet C g))=
      -sourcePair (W (phaseGenerator g)) (W (phaseJet C g))-
        sourcePair (W g) (W (phaseGenerator (phaseJet C g))) at hr
  change z*phasePair m ell F z hz g g=
    phasePair m ell F z hz g (C g)+sourcePair (W g) (W (phaseSecond C g))-
      (2:ℂ)*sourcePair (W (phaseGenerator g)) (W (phaseJet C g))-
      (2:ℂ)*sourcePair (W g) (W (phaseGenerator (phaseJet C g)))-
      sourcePair (S g) (thetaAction m ell g)
  linear_combination (norm:=ring) hf+(2:ℂ)*hr

/-- Quadratic frequency returns the whole same-CF square, including all contact slots. -/
theorem actual_phase_whole_square_frequency_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let R:=resolventCore F z hz
    let C:=compressionCore F
    let W:=thetaAction m ell*R
    let X:=thetaAction m ell*phaseJet R
    let S:=thetaAction m ell*phaseSecond R
    (z^2)*phasePair m ell F z hz g g=
      phasePair m ell F z hz g ((C*C) g)+sourcePair (W g) (W (phaseSecond (C*C) g))-
        (2:ℂ)*sourcePair (W (phaseGenerator g)) (W (phaseJet (C*C) g))-
        (2:ℂ)*sourcePair (W g) (W (phaseGenerator (phaseJet (C*C) g)))-
        (2:ℂ)*sourcePair (X g) (thetaAction m ell (phaseJet C g))-
        sourcePair (W g) (thetaAction m ell (phaseSecond C g))-
        sourcePair (S g) (thetaAction m ell (C g))-z*sourcePair (S g) (thetaAction m ell g) := by
  dsimp only
  let R:=resolventCore F z hz
  let C:=compressionCore F
  let W:=thetaAction m ell*R
  let X:=thetaAction m ell*phaseJet R
  let S:=thetaAction m ell*phaseSecond R
  have hw(q:QuantumTest):(z^2) • W q=W ((C*C) q)-thetaAction m ell (C q)-z • thetaAction m ell q := by
    have h:=congrArg (fun T:End=>thetaAction m ell (T q)) (resolvent_square_return F z hz)
    simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,map_add,map_smul] at h
    change W ((C*C) q)=thetaAction m ell (C q)+z • thetaAction m ell q+(z^2) • W q at h
    rw [h]
    module
  have hx(q:QuantumTest):(z^2) • X q=X ((C*C) q)+W (phaseJet (C*C) q)-thetaAction m ell (phaseJet C q) := by
    have h:=congrArg (fun T:End=>thetaAction m ell (T q)) (actual_phase_first_square_frequency F z hz)
    simpa only [X,W,R,C,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
      Module.End.mul_apply,map_smul,map_add,map_sub] using h
  have hs(q:QuantumTest):(z^2) • S q=S ((C*C) q)+W (phaseSecond (C*C) q)+
      (2:ℂ) • X (phaseJet (C*C) q)-thetaAction m ell (phaseSecond C q) := by
    have h:=congrArg (fun T:End=>thetaAction m ell (T q)) (actual_phase_square_frequency F z hz)
    simpa only [S,X,W,R,C,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
      Module.End.mul_apply,map_smul,map_add,map_sub] using h
  have hf:(z^2)*phasePair m ell F z hz g g=
      phasePair m ell F z hz g ((C*C) g)+sourcePair (W g) (W (phaseSecond (C*C) g))+
        (2:ℂ)*sourcePair (X g) (W (phaseJet (C*C) g))+(2:ℂ)*sourcePair (W g) (X (phaseJet (C*C) g))-
        (2:ℂ)*sourcePair (X g) (thetaAction m ell (phaseJet C g))-
        sourcePair (W g) (thetaAction m ell (phaseSecond C g))-
        sourcePair (S g) (thetaAction m ell (C g))-z*sourcePair (S g) (thetaAction m ell g) := by
    simp only [phasePair,coreWindow,Module.End.mul_apply]
    change (z^2)*((2:ℂ)*sourcePair (X g) (X g)+sourcePair (W g) (S g)+sourcePair (S g) (W g))=
      ((2:ℂ)*sourcePair (X g) (X ((C*C) g))+sourcePair (W g) (S ((C*C) g))+sourcePair (S g) (W ((C*C) g)))+
      sourcePair (W g) (W (phaseSecond (C*C) g))+(2:ℂ)*sourcePair (X g) (W (phaseJet (C*C) g))+
      (2:ℂ)*sourcePair (W g) (X (phaseJet (C*C) g))-(2:ℂ)*sourcePair (X g) (thetaAction m ell (phaseJet C g))-
      sourcePair (W g) (thetaAction m ell (phaseSecond C g))-
      sourcePair (S g) (thetaAction m ell (C g))-z*sourcePair (S g) (thetaAction m ell g)
    calc
      _=(2:ℂ)*sourcePair (X g) ((z^2) • X g)+sourcePair (W g) ((z^2) • S g)+sourcePair (S g) ((z^2) • W g) := by
        simp only [(paid_phase_frequency% pair_smul_right)]
        ring
      _=_ := by
        rw [hx,hs,hw]
        simp only [(paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_sub_right),
          (paid_phase_frequency% pair_smul_right)]
        ring
  have hr:=phase_pair_comm_return m ell F z hz g (phaseJet (C*C) g)
  dsimp only at hr
  change sourcePair (X g) (W (phaseJet (C*C) g))+sourcePair (W g) (X (phaseJet (C*C) g))=
      -sourcePair (W (phaseGenerator g)) (W (phaseJet (C*C) g))-
        sourcePair (W g) (W (phaseGenerator (phaseJet (C*C) g))) at hr
  change (z^2)*phasePair m ell F z hz g g=
    phasePair m ell F z hz g ((C*C) g)+sourcePair (W g) (W (phaseSecond (C*C) g))-
      (2:ℂ)*sourcePair (W (phaseGenerator g)) (W (phaseJet (C*C) g))-
      (2:ℂ)*sourcePair (W g) (W (phaseGenerator (phaseJet (C*C) g)))-
      (2:ℂ)*sourcePair (X g) (thetaAction m ell (phaseJet C g))-
      sourcePair (W g) (thetaAction m ell (phaseSecond C g))-
      sourcePair (S g) (thetaAction m ell (C g))-z*sourcePair (S g) (thetaAction m ell g)
  linear_combination (norm:=ring) hf+(2:ℂ)*hr

private theorem fixed_source_jets(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),compressionCore F g=diagonalAction g ∧
      phaseJet (compressionCore F) g=phaseJet diagonalAction g ∧
      phaseSecond (compressionCore F) g=phaseSecond diagonalAction g := by
  filter_upwards [(paid_phase_moment% fixed_compression) g,
    (paid_phase_moment% fixed_compression) (phaseGenerator g),
    (paid_phase_moment% fixed_compression) (phaseGenerator (phaseGenerator g))] with F h0 h1 h2
  refine ⟨h0,?_,?_⟩
  · simp only [phase_apply,h0,h1]
  · simp only [phase_second_apply,h0,h1,h2]

/-- Positive weighted U and full native/OwnDefect coframe current occur in one original return. -/
theorem actual_phase_weighted_U_frequency_return(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      let R:=resolventCore F z hz
      let W:=coreWindow m ell F z hz
      (phaseCoefficient:ℂ)*(sourcePair (W g) (inverseVolumeAction (W g))-
        sourcePair (W g) (thetaAction m ell (((R*(diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction)-
          R*(defectAction F*inverseVolumeAction-inverseVolumeAction*defectAction F))*R) g)))=
        phasePair m ell F z hz g (diagonalAction g)-z*phasePair m ell F z hz g g-
          (2:ℂ)*sourcePair (W (phaseGenerator g)) (W (phaseJet diagonalAction g))-
          (2:ℂ)*sourcePair (W g) (W (phaseGenerator (phaseJet diagonalAction g)))-
          sourcePair (thetaAction m ell (phaseSecond R g)) (thetaAction m ell g) := by
  filter_upwards [fixed_source_jets g] with F hF m ell z hz
  obtain ⟨h0,h1,h2⟩:=hF
  have h:=actual_phase_whole_frequency_return m ell F z hz g
  dsimp only at h
  rw [h0,h1,h2,actual_source_inverse_volume_phase_jet] at h
  have hc:(-(sourceTime 0:ℂ)^3*(‖SourceQuantumScalarChart.vacuum‖^2:ℂ))=-(phaseCoefficient:ℂ) := by
    simp only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul]
  rw [hc] at h
  simp only [LinearMap.smul_apply,map_smul,(paid_phase_frequency% pair_smul_right)] at h
  have hw:=actual_weighted_window_input m ell F z hz g g
  rw [actual_coframe_flux_source] at hw
  simp only [coreWindow,Module.End.mul_apply,LinearMap.sub_apply,map_sub,
    (paid_phase_frequency% pair_sub_right),mul_sub,sub_mul] at h hw ⊢
  linear_combination (norm:=ring) h+(phaseCoefficient:ℂ)*hw

private theorem fixed_source_square_jets(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),
      (compressionCore F*compressionCore F) g=(diagonalAction*diagonalAction) g ∧
      phaseJet (compressionCore F*compressionCore F) g=phaseJet (diagonalAction*diagonalAction) g ∧
      phaseSecond (compressionCore F*compressionCore F) g=phaseSecond (diagonalAction*diagonalAction) g := by
  filter_upwards [(paid_phase_moment% fixed_compression) g,
    (paid_phase_moment% fixed_compression) (diagonalAction g),
    (paid_phase_moment% fixed_compression) (phaseGenerator g),
    (paid_phase_moment% fixed_compression) (diagonalAction (phaseGenerator g)),
    (paid_phase_moment% fixed_compression) (phaseGenerator (phaseGenerator g)),
    (paid_phase_moment% fixed_compression) (diagonalAction (phaseGenerator (phaseGenerator g)))]
    with F h0 hH h1 hH1 h2 hH2
  have he0:(compressionCore F*compressionCore F) g=(diagonalAction*diagonalAction) g := by
    simp only [Module.End.mul_apply,h0,hH]
  have he1:(compressionCore F*compressionCore F) (phaseGenerator g)=
      (diagonalAction*diagonalAction) (phaseGenerator g) := by
    simp only [Module.End.mul_apply,h1,hH1]
  have he2:(compressionCore F*compressionCore F) (phaseGenerator (phaseGenerator g))=
      (diagonalAction*diagonalAction) (phaseGenerator (phaseGenerator g)) := by
    simp only [Module.End.mul_apply,h2,hH2]
  refine ⟨he0,?_,?_⟩
  · simp only [phase_apply,he0,he1]
  · simp only [phase_second_apply,he0,he1,he2]

/-- Fixed original source jets force the quadratic return on one cofinal F for every cutoff. -/
theorem actual_source_phase_square_frequency_return(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      let R:=resolventCore F z hz
      let W:=thetaAction m ell*R
      let X:=thetaAction m ell*phaseJet R
      let S:=thetaAction m ell*phaseSecond R
      (z^2)*phasePair m ell F z hz g g=
        phasePair m ell F z hz g ((diagonalAction*diagonalAction) g)+
        sourcePair (W g) (W (phaseSecond (diagonalAction*diagonalAction) g))-
          (2:ℂ)*sourcePair (W (phaseGenerator g)) (W (phaseJet (diagonalAction*diagonalAction) g))-
          (2:ℂ)*sourcePair (W g) (W (phaseGenerator (phaseJet (diagonalAction*diagonalAction) g)))-
          (2:ℂ)*sourcePair (X g) (thetaAction m ell (phaseJet diagonalAction g))+
          (phaseCoefficient:ℂ)*sourcePair (W g) (thetaAction m ell (inverseVolumeAction g))-
          sourcePair (S g) (thetaAction m ell (diagonalAction g))-
          z*sourcePair (S g) (thetaAction m ell g) := by
  filter_upwards [fixed_source_jets g,fixed_source_square_jets g] with F hF hSq m ell z hz
  obtain ⟨h0,h1,h2⟩:=hF
  obtain ⟨hs0,hs1,hs2⟩:=hSq
  have h:=actual_phase_whole_square_frequency_return m ell F z hz g
  dsimp only at h ⊢
  rw [hs0,hs1,hs2,h0,h1,h2,actual_source_inverse_volume_phase_jet] at h
  simp only [LinearMap.smul_apply,map_smul,(paid_phase_frequency% pair_smul_right)] at h
  simpa only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul,mul_neg,sub_neg_eq_add] using h

/-- The native inverse scale returns through its fixed source input and both real currents. -/
def scaleFlux(F:Index)(z:ℂ)(hz:z.im≠0):End :=
  resolventCore F z hz*(compressionCore F*SourceScalarInverseBulk.inverseSymmetricScale-
    SourceScalarInverseBulk.inverseSymmetricScale*compressionCore F)*resolventCore F z hz

theorem actual_source_scale_flux(F:Index)(z:ℂ)(hz:z.im≠0):
    scaleFlux F z hz=
      resolventCore F z hz*(diagonalAction*SourceScalarInverseBulk.inverseSymmetricScale-
        SourceScalarInverseBulk.inverseSymmetricScale*diagonalAction)*resolventCore F z hz-
      resolventCore F z hz*(defectAction F*SourceScalarInverseBulk.inverseSymmetricScale-
        SourceScalarInverseBulk.inverseSymmetricScale*defectAction F)*resolventCore F z hz := by
  have hc:compressionCore F=diagonalAction-defectAction F := by unfold defectAction;abel
  unfold scaleFlux
  rw [hc]
  noncomm_ring

private theorem scale_input(F:Index)(z:ℂ)(hz:z.im≠0):
    SourceScalarInverseBulk.inverseSymmetricScale*resolventCore F z hz=
      resolventCore F z hz*SourceScalarInverseBulk.inverseSymmetricScale+scaleFlux F z hz := by
  have hi:=(paid_phase_inverse% actual_inverse) F z hz
  have h:=(paid_phase_inverse% inverse_comm) (compressionCore F-z • (1:End))
    (resolventCore F z hz) SourceScalarInverseBulk.inverseSymmetricScale hi.1 hi.2
  simp only [(paid_phase_inverse% comm_spectral)] at h
  change SourceScalarInverseBulk.inverseSymmetricScale*resolventCore F z hz-
      resolventCore F z hz*SourceScalarInverseBulk.inverseSymmetricScale=
    -resolventCore F z hz*(SourceScalarInverseBulk.inverseSymmetricScale*compressionCore F-
      compressionCore F*SourceScalarInverseBulk.inverseSymmetricScale)*resolventCore F z hz at h
  unfold scaleFlux
  linear_combination (norm:=noncomm_ring) h

def compensatedScale(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  let W:=coreWindow m ell F z hz
  sourcePair (W g) (SourceScalarInverseBulk.inverseSymmetricScale (W g))-
    sourcePair (W g) (thetaAction m ell (scaleFlux F z hz g))-
    sourcePair (W g) ((SourceScalarInverseBulk.inverseSymmetricScale*thetaAction m ell-
      thetaAction m ell*SourceScalarInverseBulk.inverseSymmetricScale) (resolventCore F z hz g))

theorem actual_weighted_scale_input(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    compensatedScale m ell F z hz g=
      sourcePair (coreWindow m ell F z hz g)
        (coreWindow m ell F z hz (SourceScalarInverseBulk.inverseSymmetricScale g)) := by
  let A:=SourceScalarInverseBulk.inverseSymmetricScale
  have hs:=LinearMap.congr_fun (scale_input F z hz) g
  change A (resolventCore F z hz g)=resolventCore F z hz (A g)+scaleFlux F z hz g at hs
  have ht:A (thetaAction m ell (resolventCore F z hz g))=
      thetaAction m ell (A (resolventCore F z hz g))+
      (A*thetaAction m ell-thetaAction m ell*A) (resolventCore F z hz g) := by
    simp only [Module.End.mul_apply,LinearMap.sub_apply]
    module
  simp only [compensatedScale,coreWindow,Module.End.mul_apply]
  change sourcePair (thetaAction m ell (resolventCore F z hz g))
      (A (thetaAction m ell (resolventCore F z hz g)))-
      sourcePair (thetaAction m ell (resolventCore F z hz g)) (thetaAction m ell (scaleFlux F z hz g))-
      sourcePair (thetaAction m ell (resolventCore F z hz g))
        ((A*thetaAction m ell-thetaAction m ell*A) (resolventCore F z hz g))=_
  rw [ht,hs]
  simp only [map_add,(paid_phase_frequency% pair_add_right)]
  ring

attribute [local irreducible] compensatedScale scaleFlux

/-- Actual weighted native scale, full CF flux, radial commutator and the negative-force
source square enter the same quadratic return. No flux tail or positive price is supplied. -/
theorem actual_weighted_scale_phase_square_return(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      let R:=resolventCore F z hz
      let W:=thetaAction m ell*R
      let X:=thetaAction m ell*phaseJet R
      let S:=thetaAction m ell*phaseSecond R
      (2*(phaseCoefficient:ℂ))*compensatedScale m ell F z hz g=
        phasePair m ell F z hz g ((diagonalAction*diagonalAction) g)-(z^2)*phasePair m ell F z hz g g-
          (2:ℂ)*sourcePair (W (phaseGenerator g)) (W (phaseJet (diagonalAction*diagonalAction) g))-
          (2:ℂ)*sourcePair (W g) (W (phaseGenerator (phaseJet (diagonalAction*diagonalAction) g)))-
          (2:ℂ)*sourcePair (X g) (thetaAction m ell (phaseJet diagonalAction g))+
          (phaseCoefficient:ℂ)*sourcePair (W g) (thetaAction m ell (inverseVolumeAction g))-
          sourcePair (S g) (thetaAction m ell (diagonalAction g))-
          z*sourcePair (S g) (thetaAction m ell g)+
          (2:ℂ)*sourcePair (W g) (W ((ActualPhaseBulkSquare.phaseForce*ActualPhaseBulkSquare.phaseForce) g)) := by
  filter_upwards [actual_source_phase_square_frequency_return g] with F hF m ell z hz
  have h:=hF m ell z hz
  dsimp only at h ⊢
  have hs:=congrArg (fun A:End=>sourcePair (coreWindow m ell F z hz g)
    (coreWindow m ell F z hz (A g))) ActualPhaseBulkSquare.actual_inverse_symmetric_phase_balance
  simp only [LinearMap.smul_apply,LinearMap.add_apply,LinearMap.neg_apply,map_smul,map_add,map_neg,
    (paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_smul_right),
    pair_neg_right,ActualPhaseBulkSquare.phaseHamiltonianSquare] at hs
  change (2*(phaseCoefficient:ℂ))*sourcePair (coreWindow m ell F z hz g)
      (coreWindow m ell F z hz (SourceScalarInverseBulk.inverseSymmetricScale g))=
    -sourcePair (coreWindow m ell F z hz g)
      (coreWindow m ell F z hz (phaseSecond (diagonalAction*diagonalAction) g))+
    (2:ℂ)*sourcePair (coreWindow m ell F z hz g)
      (coreWindow m ell F z hz ((ActualPhaseBulkSquare.phaseForce*ActualPhaseBulkSquare.phaseForce) g)) at hs
  rw [actual_weighted_scale_input]
  simp only [coreWindow,Module.End.mul_apply] at h hs ⊢
  linear_combination (norm:=ring) h+hs

theorem actual_phase_second_resolvent_spectral(F:Index)(z:ℂ)(hz:z.im≠0):
    phaseSecond (resolventCore F z hz)=
      ∑ i:SpectralIndex F,(((channelValue F (some i):ℂ)-z)⁻¹+z⁻¹) • phaseSecond (channelCore F (some i)) := by
  rw [(paid_phase_frequency% core_resolvent_spectral),map_add,map_smul,map_sum,phase_second_one,smul_zero,zero_add]
  simp only [map_smul]

/-- Complete finite spectral projection cancels the escape pole before either cause is integrated. -/
theorem actual_phase_whole_endpoint_pair_integral(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g h:QuantumTest):
    let endpoint:=fun w:ℝ=>sourcePair
      (thetaAction m ell (phaseSecond (resolventCore F (causalFrequency advanced μ w)
        ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)) g)) (thetaAction m ell h)
    Integrable endpoint ∧ (∫w:ℝ,endpoint w)=0 := by
  classical
  dsimp only
  let c(i:SpectralIndex F):ℂ:=sourcePair
    (thetaAction m ell (phaseSecond (channelCore F (some i)) g)) (thetaAction m ell h)
  have he(w:ℝ):sourcePair
      (thetaAction m ell (phaseSecond (resolventCore F (causalFrequency advanced μ w)
        ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)) g)) (thetaAction m ell h)=
      ∑i:SpectralIndex F,star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)*c i := by
    rw [actual_phase_second_resolvent_spectral]
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,sourcePair,
      sum_inner,inner_smul_left,starRingEnd_apply]
    simp only [c,sourcePair]
    rfl
  have hi (i : SpectralIndex F) : Integrable (fun w : ℝ =>
      star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)*c i) :=
    ((paid_phase_frequency% causal_star_return_integrable) advanced μ _ hμ).mul_const _
  constructor
  · simp_rw [he]
    exact integrable_finsetSum _ (fun i _=>hi i)
  · simp_rw [he]
    rw [integral_finsetSum Finset.univ (fun i _=>hi i)]
    simp only [integral_mul_const,(paid_phase_frequency% causal_star_return_integral) advanced μ _ hμ,
      zero_mul,Finset.sum_const_zero]


theorem actual_phase_whole_endpoint_integral(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g:QuantumTest):
    let endpoint:=fun w:ℝ=>sourcePair
      (thetaAction m ell (phaseSecond (resolventCore F (causalFrequency advanced μ w)
        ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)) g)) (thetaAction m ell g)
    Integrable endpoint ∧ (∫w:ℝ,endpoint w)=0 :=
  actual_phase_whole_endpoint_pair_integral advanced μ hμ m ell F g g

end LowEnergy.ActualScalarPhaseFrequencyReturn
