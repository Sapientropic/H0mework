import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedN1SlopePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedSlopeGrowth
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedLeftFreeJet

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCompletePrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumNoetherChart PreparationVacuumActionFieldLift
open ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNumberZero
open ActualDressedNumberField ActualDressedPreparedPrice ActualDressedN1Price ActualDressedLeftFreeJet
open SourceGraph PreparationVacuumSourcePreparedResponse
open scoped Topology InnerProductSpace BigOperators
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointCompression jointCResolvent noetherReader jointResolvent physicalTime timeSlope
  sourceDressedUnit prepared sourceProfile jointCurrent dressedNoetherJet dressedEulerObserver dressedNoetherKernel
  numberFieldRead freeTimeSlope freeCompressionCurrent actualA

private def fourSlope {R : Type*} [Ring R] (A B C D dA dB dC dD : R) : R :=
  dA*B*C*D+A*dB*C*D+A*B*dC*D+A*B*C*dD

private def fiveSlope {R : Type*} [Ring R] (A B C D T dA dB dC dD dT : R) : R :=
  fourSlope A B C D dA dB dC dD*T+A*B*C*D*dT

private theorem five_derivative {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A B C D T : ℝ→R) (dA dB dC dD dT : R)
    (ha : HasDerivAt A dA 0) (hb : HasDerivAt B dB 0) (hc : HasDerivAt C dC 0)
    (hd : HasDerivAt D dD 0) (ht : HasDerivAt T dT 0) :
    HasDerivAt (fun r => A r*B r*C r*D r*T r)
      (fiveSlope (A 0) (B 0) (C 0) (D 0) (T 0) dA dB dC dD dT) 0 := by
  have source:=(((ha.mul hb).mul hc).mul hd).mul ht
  have coefficient :
      ((((dA*B 0+A 0*dB)*C 0+(A*B) 0*dC)*D 0+(A*B*C) 0*dD)*T 0+(A*B*C*D) 0*dT)=
        fiveSlope (A 0) (B 0) (C 0) (D 0) (T 0) dA dB dC dD dT := by
    simp only [Pi.mul_apply]
    unfold fiveSlope fourSlope
    noncomm_ring
  exact source.congr_deriv coefficient

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem four_norm (A B C D : E→L[ℂ]E) :
    ‖A*B*C*D‖  ≤  ‖A‖*‖B‖*‖C‖*‖D‖ := by
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg C))) (norm_nonneg D))

private theorem four_slope_norm (A B C D dA dB dC dD : E→L[ℂ]E) :
    ‖fourSlope A B C D dA dB dC dD‖  ≤
      ‖dA‖*‖B‖*‖C‖*‖D‖+‖A‖*‖dB‖*‖C‖*‖D‖+
        ‖A‖*‖B‖*‖dC‖*‖D‖+‖A‖*‖B‖*‖C‖*‖dD‖ := by
  unfold fourSlope
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (four_norm _ _ _ _) (four_norm _ _ _ _)))
      (four_norm _ _ _ _))) (four_norm _ _ _ _))

private theorem four_slope_price (A B C D dA dB dC dD : E→L[ℂ]E)
    (t cp bp cp' dp : ℝ) (ht : 0 ≤ t) (hcp : 0 ≤ cp) (hbp : 0 ≤ bp) (hcp' : 0 ≤ cp') (hdp : 0 ≤ dp)
    (a : ‖A‖ ≤ 1) (da : ‖dA‖ ≤ t*cp) (db : ‖dB‖ ≤ bp) (dc : ‖dC‖ ≤ cp') (dd : ‖dD‖ ≤ dp) :
    ‖fourSlope A B C D dA dB dC dD‖  ≤  (1+t)*
      (cp*‖B‖*‖C‖*‖D‖+bp*‖C‖*‖D‖+‖B‖*cp'*‖D‖+‖B‖*‖C‖*dp) := by
  have coarse : ‖fourSlope A B C D dA dB dC dD‖  ≤
      t*cp*‖B‖*‖C‖*‖D‖+bp*‖C‖*‖D‖+‖B‖*cp'*‖D‖+‖B‖*‖C‖*dp := by
    refine (four_slope_norm _ _ _ _ _ _ _ _).trans ?_
    calc
      _ ≤ (t*cp)*‖B‖*‖C‖*‖D‖+1*bp*‖C‖*‖D‖+1*‖B‖*cp'*‖D‖+1*‖B‖*‖C‖*dp := by gcongr
      _=_:=by ring
  have rest : 0 ≤ bp*‖C‖*‖D‖+‖B‖*cp'*‖D‖+‖B‖*‖C‖*dp:=by positivity
  have first : 0 ≤ cp*‖B‖*‖C‖*‖D‖:=by positivity
  exact coarse.trans (by nlinarith [mul_nonneg ht rest])

private theorem five_vector_price (A B C D T dA dB dC dD dT : E→L[ℂ]E)
    (t c m n : ℝ) (ht : 0 ≤ t) (hc : 0 ≤ c) (hm : 0 ≤ m) (x : E)
    (a : ‖A‖ ≤ 1) (four : ‖fourSlope A B C D dA dB dC dD‖ ≤ (1+t)*c)
    (time : ‖T x‖ ≤ m*(1+t)^2*‖x‖) (slope : ‖dT x‖ ≤ n*‖x‖*(1+t)^5) :
    ‖fiveSlope A B C D T dA dB dC dD dT x‖  ≤
      (c*m+‖B‖*‖C‖*‖D‖*n)*‖x‖*(1+t)^5 := by
  have product : ‖A*B*C*D‖ ≤ ‖B‖*‖C‖*‖D‖ := by
    refine (four_norm _ _ _ _).trans ?_
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right a (norm_nonneg B)) (norm_nonneg C)) (norm_nonneg D)
  have powers : (1+t)^3 ≤ (1+t)^5:=pow_le_pow_right₀ (by linarith) (by norm_num : 3 ≤ 5)
  calc
    _ ≤ ‖fourSlope A B C D dA dB dC dD (T x)‖+‖(A*B*C*D) (dT x)‖:=by
      simpa only [fiveSlope,add_apply,mul_apply_eq_comp] using norm_add_le
        (fourSlope A B C D dA dB dC dD (T x)) ((A*B*C*D) (dT x))
    _ ≤ ((1+t)*c)*(m*(1+t)^2*‖x‖)+(‖B‖*‖C‖*‖D‖)*(n*‖x‖*(1+t)^5):=by
      exact add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul four time (norm_nonneg _) (by positivity)))
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul product slope (norm_nonneg _) (by positivity)))
    _=c*m*‖x‖*(1+t)^3+(‖B‖*‖C‖*‖D‖*n)*‖x‖*(1+t)^5:=by ring
    _ ≤ c*m*‖x‖*(1+t)^5+(‖B‖*‖C‖*‖D‖*n)*‖x‖*(1+t)^5:=by
      exact add_le_add (mul_le_mul_of_nonneg_left powers (by positivity)) le_rfl
    _=_:=by ring

private theorem time_norm_price (C : E→L[ℂ]E) (symmetric : IsSelfAdjoint C) (t : ℝ) :
    ‖SourceFiniteUnitary.time C t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [SourceFiniteUnitary.time_norm C symmetric,one_mul]

private theorem insertion_price (U B : E→L[ℂ]E) : ‖-(U*B*U)‖ ≤ ‖U‖^2*‖B‖ := by
  rw [norm_neg]
  exact ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg U))).trans_eq (by ring)

omit [CompleteSpace E] in
private theorem paired_price (Q : E→L[ℂ]E) (x y : E) (c t : ℝ)
    (hx : ‖Q x‖ ≤ c*‖x‖*t) (hy : ‖Q y‖ ≤ c*‖y‖*t) :
    ‖-inner ℂ x (Q x)+inner ℂ y (Q y)‖ ≤ (c*(‖x‖^2+‖y‖^2))*t := by
  calc
    _ ≤ ‖inner ℂ x (Q x)‖+‖inner ℂ y (Q y)‖:=by simpa only [norm_neg] using norm_add_le (-inner ℂ x (Q x)) (inner ℂ y (Q y))
    _ ≤ ‖x‖*‖Q x‖+‖y‖*‖Q y‖:=add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x‖*(c*‖x‖*t)+‖y‖*(c*‖y‖*t):=add_le_add
      (mul_le_mul_of_nonneg_left hx (norm_nonneg x)) (mul_le_mul_of_nonneg_left hy (norm_nonneg y))
    _=_:=by ring
end Generic

private theorem occupation_one_le_two (a t : ℝ) : occupationPrice 1 a t ≤ occupationPrice 2 a t := by
  have one : occupationPrice 1 a t=1+t*a:=by simp [occupationPrice,Finset.sum_range_succ]
  rw [one,occupationPrice_two]
  exact le_add_of_nonneg_right (sq_nonneg _)

private theorem occupation_time_growth (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (x : H) (sector : ActualDressedNumberSector.numberTwoProjection x=x ∨
      PreparationVacuumPhysicalN1WardCollapse.sourceN1Projection x=x) :
    ‖physicalTime p F t 0 x‖ ≤ (1+‖actualA p F‖)^2*(1+|t|)^2*‖x‖ := by
  have base : ‖physicalTime p F t 0 x‖ ≤ occupationPrice 2 ‖actualA p F‖ |t| *‖x‖ := by
    rcases sector with hn2|hn1
    · exact actual_time_N2_price p F t x hn2
    · exact (actual_time_N1_price p F t x hn1).trans
        (mul_le_mul_of_nonneg_right (occupation_one_le_two _ _) (norm_nonneg x))
  exact base.trans (mul_le_mul_of_nonneg_right
    (occupationPrice_two_growth _ _ (norm_nonneg _) (abs_nonneg t)) (norm_nonneg x))

private theorem scalar_slope_growth (a j v t : ℝ) (ha : 0 ≤ a) (hj : 0 ≤ j) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    t*j*(occupationPrice 2 a t)^2*v ≤ (j*(1+a)^4*v)*(1+t)^5 := by
  have square : (occupationPrice 2 a t)^2 ≤ (1+a)^4*(1+t)^4:=
    (pow_le_pow_left₀ (occupationPrice_nonneg 2 a t ha ht)
      (occupationPrice_two_growth a t ha ht) 2).trans_eq (by ring)
  calc
    _ ≤ ((1+t)*j)*((1+a)^4*(1+t)^4)*v:=by
      apply mul_le_mul_of_nonneg_right _ hv
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hj) square (sq_nonneg _) (by positivity)
    _=_:=by ring

private theorem occupation_slope_growth (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) (t : ℝ) (x : H) (sector : ActualDressedNumberSector.numberTwoProjection x=x ∨
      PreparationVacuumPhysicalN1WardCollapse.sourceN1Projection x=x) :
    ‖timeSlope force p F t x‖ ≤
      (‖jointCurrent p F 0 0 force‖*(1+‖actualA p F‖)^4*‖x‖)*(1+|t|)^5 := by
  rcases sector with hn2|hn1
  · exact actual_timeSlope_N2_polynomial_price p F force x hn2 t
  · have square:=pow_le_pow_left₀ (occupationPrice_nonneg 1 ‖actualA p F‖ |t| (norm_nonneg _) (abs_nonneg t))
      (occupation_one_le_two ‖actualA p F‖ |t|) 2
    have source:=(actual_timeSlope_N1_price p F force t x hn1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left square
        (mul_nonneg (abs_nonneg t) (norm_nonneg _))) (norm_nonneg x))
    exact source.trans (scalar_slope_growth _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (abs_nonneg t))

/-- The same actual insertion, retaining its complete reader and full right Green, with the paid grade-zero left field germ. -/
def leftFreeKernel (event : DressedEvent) (transfer : PhysicalMomentum) (reader : Field289)
    (t : ℝ) (h : Field289) : H→L[ℂ]H :=
  SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-t)*
    jointCResolvent (event.momentum-transfer) event.frame event.energy h*
      noetherReader reader event.momentum event.frame h*
        jointResolvent event.momentum event.frame event.energy h*physicalTime event.momentum event.frame t h
attribute [local irreducible] leftFreeKernel

def leftFreeRead (event : DressedEvent) (transfer : PhysicalMomentum) (reader : Field289)
    (t : ℝ) (h : Field289) : ℂ :=
  -inner ℂ (sourceDressedUnit event.epsilon event.precision)
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-t)
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h
        (noetherReader reader event.momentum event.frame h
          (jointResolvent event.momentum event.frame event.energy h
            (physicalTime event.momentum event.frame t h (sourceDressedUnit event.epsilon event.precision))))))+
  inner ℂ (prepared (sourceProfile event.epsilon event.precision))
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-t)
      (jointCResolvent (event.momentum-transfer) event.frame event.energy h
        (noetherReader reader event.momentum event.frame h
          (jointResolvent event.momentum event.frame event.energy h
            (physicalTime event.momentum event.frame t h (prepared (sourceProfile event.epsilon event.precision)))))))
attribute [local irreducible] leftFreeRead

theorem actual_left_free_read_germ (event : DressedEvent) (transfer : PhysicalMomentum) :
    ∀ᶠh : Field289 in 𝓝 0,∀(t : ℝ) (reader : Field289),
    dressedEulerObserver event (dressedNoetherKernel event transfer reader t h)=
      leftFreeRead event transfer reader t h := by
  filter_upwards [actual_noether_number_field_germ event transfer,
    actual_joint_created_inverse_time_return event.momentum event.frame event.energy event.nonreal event.epsilon event.precision,
    actual_joint_background_inverse_time_return event.momentum event.frame event.energy event.nonreal
      (sourceProfile event.epsilon event.precision)] with h source created background
  intro t reader
  refine (source t reader).trans ?_
  unfold numberFieldRead leftFreeRead
  exact congrArg₂ (fun x y : H=>
    -inner ℂ (sourceDressedUnit event.epsilon event.precision)
      (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-t)
        (jointCResolvent (event.momentum-transfer) event.frame event.energy h
          (noetherReader reader event.momentum event.frame h x)))+
    inner ℂ (prepared (sourceProfile event.epsilon event.precision))
      (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame h) (-t)
        (jointCResolvent (event.momentum-transfer) event.frame event.energy h
          (noetherReader reader event.momentum event.frame h y))))
    (created t).symm (background t).symm

private theorem kernel_direction (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (t : ℝ) :
    HasDerivAt (fun r : ℝ => leftFreeKernel event transfer reader t (r • force))
      (fiveSlope
        (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame 0) (-t))
        (jointCResolvent (event.momentum-transfer) event.frame event.energy 0)
        (noetherReader reader event.momentum event.frame 0)
        (jointResolvent event.momentum event.frame event.energy 0)
        (physicalTime event.momentum event.frame t 0)
        (freeTimeSlope (event.momentum-transfer) event.frame force (-t))
        (-(jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
          freeCompressionCurrent (event.momentum-transfer) event.frame force*
            jointCResolvent (event.momentum-transfer) event.frame event.energy 0))
        (noetherReaderContact reader force event.momentum event.frame)
        (-(jointResolvent event.momentum event.frame event.energy 0*
          jointCurrent event.momentum event.frame event.energy 0 force*
            jointResolvent event.momentum event.frame event.energy 0))
        (timeSlope force event.momentum event.frame t)) 0 := by
  have source:=five_derivative _ _ _ _ _ _ _ _ _ _
    (free_time_direction (event.momentum-transfer) event.frame force (-t))
    (free_green_direction (event.momentum-transfer) event.frame event.energy event.nonreal force)
    (noetherReader_generated reader force event.momentum event.frame)
    (inverse_direction event.momentum event.frame event.energy event.nonreal force)
    (physicalTime_direction force event.momentum event.frame t)
  simpa only [zero_smul,leftFreeKernel] using source


private def kernelSlope (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (t : ℝ) : H→L[ℂ]H :=
  fiveSlope
    (SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame 0) (-t))
    (jointCResolvent (event.momentum-transfer) event.frame event.energy 0)
    (noetherReader reader event.momentum event.frame 0)
    (jointResolvent event.momentum event.frame event.energy 0)
    (physicalTime event.momentum event.frame t 0)
    (freeTimeSlope (event.momentum-transfer) event.frame force (-t))
    (-(jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
      freeCompressionCurrent (event.momentum-transfer) event.frame force*
        jointCResolvent (event.momentum-transfer) event.frame event.energy 0))
    (noetherReaderContact reader force event.momentum event.frame)
    (-(jointResolvent event.momentum event.frame event.energy 0*
      jointCurrent event.momentum event.frame event.energy 0 force*
        jointResolvent event.momentum event.frame event.energy 0))
    (timeSlope force event.momentum event.frame t)
attribute [local irreducible] kernelSlope

private def fourPriceCore (cp b c d contact jg : ℝ) : ℝ :=
  cp*b*c*d+b^2*cp*c*d+b*contact*d+b*c*(d^2*jg)

private theorem fourPriceCore_nonneg (cp b c d contact jg : ℝ)
    (hp : 0 ≤ cp) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ contact) (hg : 0 ≤ jg) :
    0 ≤ fourPriceCore cp b c d contact jg := by
  unfold fourPriceCore
  positivity

private def priceCore (cp b c d contact jg jt a : ℝ) : ℝ :=
  fourPriceCore cp b c d contact jg*(1+a)^2+b*c*d*(jt*(1+a)^4)

private theorem priceCore_nonneg (cp b c d contact jg jt a : ℝ)
    (hp : 0 ≤ cp) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ contact)
    (hg : 0 ≤ jg) (ht : 0 ≤ jt) (ha : 0 ≤ a) : 0 ≤ priceCore cp b c d contact jg jt a := by
  unfold priceCore fourPriceCore
  positivity

private def kernelPrice (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) : ℝ :=
  priceCore
    ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖
    ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖
    ‖noetherReader reader event.momentum event.frame 0‖
    ‖jointResolvent event.momentum event.frame event.energy 0‖
    ‖noetherReaderContact reader force event.momentum event.frame‖
    ‖jointCurrent event.momentum event.frame event.energy 0 force‖
    ‖jointCurrent event.momentum event.frame 0 0 force‖
    ‖actualA event.momentum event.frame‖
attribute [local irreducible] kernelPrice

private theorem kernel_slope_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (t : ℝ) (x : H)
    (sector : ActualDressedNumberSector.numberTwoProjection x=x ∨
      PreparationVacuumPhysicalN1WardCollapse.sourceN1Projection x=x) :
    ‖kernelSlope event transfer reader force t x‖ ≤ kernelPrice event transfer reader force*‖x‖*(1+|t|)^5 := by
  let A:=SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame 0) (-t)
  let B:=jointCResolvent (event.momentum-transfer) event.frame event.energy 0
  let C:=noetherReader reader event.momentum event.frame 0
  let D:=jointResolvent event.momentum event.frame event.energy 0
  let T:=physicalTime event.momentum event.frame t 0
  let cp:=‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖
  let jg:=‖jointCurrent event.momentum event.frame event.energy 0 force‖
  let jt:=‖jointCurrent event.momentum event.frame 0 0 force‖
  let a:=‖actualA event.momentum event.frame‖
  let contact:=noetherReaderContact reader force event.momentum event.frame
  let dA:=freeTimeSlope (event.momentum-transfer) event.frame force (-t)
  let dB:=-(B*freeCompressionCurrent (event.momentum-transfer) event.frame force*B)
  let dD:=-(D*jointCurrent event.momentum event.frame event.energy 0 force*D)
  let dT:=timeSlope force event.momentum event.frame t
  let c:=fourPriceCore cp ‖B‖ ‖C‖ ‖D‖ ‖contact‖ jg
  have ac : ‖A‖ ≤ 1 := by
    dsimp only [A]
    rw [free_compression_base]
    exact time_norm_price _ (CanonicalPhysicalSpatial.compression_selfAdjoint _ _) (-t)
  have dac : ‖dA‖ ≤ |t| *cp := by
    simpa only [dA,cp,abs_neg] using free_time_slope_price (event.momentum-transfer) event.frame force (-t)
  have dbc : ‖dB‖ ≤ ‖B‖^2*cp:=free_green_slope_price (event.momentum-transfer) event.frame event.energy force
  have ddc : ‖dD‖ ≤ ‖D‖^2*jg:=insertion_price D (jointCurrent event.momentum event.frame event.energy 0 force)
  have four : ‖fourSlope A B C D dA dB contact dD‖ ≤ (1+|t|)*c := by
    exact four_slope_price A B C D dA dB contact dD |t| cp (‖B‖^2*cp) ‖contact‖ (‖D‖^2*jg)
      (abs_nonneg t) (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))
      (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _)) ac dac dbc le_rfl ddc
  have time : ‖T x‖ ≤ (1+a)^2*(1+|t|)^2*‖x‖:=occupation_time_growth event.momentum event.frame t x sector
  have slope : ‖dT x‖ ≤ (jt*(1+a)^4)*‖x‖*(1+|t|)^5:=occupation_slope_growth event.momentum event.frame force t x sector
  have nonnegative : 0 ≤ c:=fourPriceCore_nonneg _ _ _ _ _ _
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have source:=five_vector_price A B C D T dA dB contact dD dT |t| c ((1+a)^2) (jt*(1+a)^4)
    (abs_nonneg t) nonnegative (sq_nonneg _) x ac four time slope
  simpa only [kernelSlope,kernelPrice,priceCore,A,B,C,D,T,dA,dB,dD,dT,c,cp,jg,jt,a,contact] using source

/-- Source-owned fixed event/reader/force coefficient; the original background norm remains visible. -/
def completeNoetherPrice (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) : ℝ :=
  kernelPrice event transfer reader force*(1+‖prepared (sourceProfile event.epsilon event.precision)‖^2)
attribute [local irreducible] completeNoetherPrice

private theorem observed_kernel_slope_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (t : ℝ) :
    ‖dressedEulerObserver event (kernelSlope event transfer reader force t)‖ ≤
      completeNoetherPrice event transfer reader force*(1+|t|)^5 := by
  have unit:=kernel_slope_price event transfer reader force t (sourceDressedUnit event.epsilon event.precision)
    (Or.inl (ActualDressedNumberSector.actual_created_unit_N2 event.epsilon event.precision))
  have background:=kernel_slope_price event transfer reader force t (prepared (sourceProfile event.epsilon event.precision))
    (Or.inr (actual_background_number_one _))
  have source:=paired_price (kernelSlope event transfer reader force t)
    (sourceDressedUnit event.epsilon event.precision) (prepared (sourceProfile event.epsilon event.precision))
    (kernelPrice event transfer reader force) ((1+|t|)^5) unit background
  rw [dressed_euler_observer_original]
  simpa only [completeNoetherPrice,source_dressed_unit_norm,one_pow] using source

private theorem left_free_read_observed (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (t : ℝ) (h : Field289) :
    leftFreeRead event transfer reader t h=dressedEulerObserver event (leftFreeKernel event transfer reader t h) := by
  rw [dressed_euler_observer_original]
  unfold leftFreeRead leftFreeKernel
  simp only [mul_apply_eq_comp]

/-- The original complete constant-force five-factor quantum jet has a source-generated fifth-degree time price. -/
theorem actual_complete_noether_jet_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (t : ℝ) (i : Fin 289) :
    ‖(dressedNoetherJet event transfer (fun _ => ⟨force,0,0⟩) t i).value‖ ≤
      completeNoetherPrice event transfer (fieldUnit i) force*(1+|t|)^5 := by
  have curve : Filter.Tendsto (fun r : ℝ => r • force) (𝓝 0) (𝓝 (0:Field289)) := by
    have continuous : Continuous (fun r : ℝ=>r • force):=continuous_id.smul continuous_const
    simpa only [zero_smul] using continuous.tendsto (0:ℝ)
  have germ:=curve.eventually (actual_left_free_read_germ event transfer)
  have original:=dressed_noether_action_derivative event transfer force t i
  have recovered:=original.congr_of_eventuallyEq (germ.mono (fun r source =>
    (source t (fieldUnit i)).trans (left_free_read_observed event transfer (fieldUnit i) t (r • force)) |>.symm))
  have direction : HasDerivAt (fun r : ℝ => leftFreeKernel event transfer (fieldUnit i) t (r • force))
      (kernelSlope event transfer (fieldUnit i) force t) 0 := by
    unfold kernelSlope
    exact kernel_direction event transfer (fieldUnit i) force t
  have generated:=((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 direction
  have same:=recovered.unique generated
  exact (congrArg norm same).le.trans (observed_kernel_slope_price event transfer (fieldUnit i) force t)

theorem complete_noether_price_nonneg (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) : 0 ≤ completeNoetherPrice event transfer reader force := by
  have core : 0 ≤ kernelPrice event transfer reader force := by
    unfold kernelPrice
    exact priceCore_nonneg _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  unfold completeNoetherPrice
  exact mul_nonneg core (add_nonneg zero_le_one (sq_nonneg _))

theorem actual_complete_noether_polynomial_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (i : Fin 289) :
    ∃K : ℝ,0 ≤ K ∧ ∀t : ℝ,‖(dressedNoetherJet event transfer (fun _ => ⟨force,0,0⟩) t i).value‖ ≤ K*(1+|t|)^5 :=
  ⟨completeNoetherPrice event transfer (fieldUnit i) force,complete_noether_price_nonneg event transfer (fieldUnit i) force,
    fun t => actual_complete_noether_jet_price event transfer force t i⟩

end LowEnergy.GaussComposite.ActualDressedCompletePrice
