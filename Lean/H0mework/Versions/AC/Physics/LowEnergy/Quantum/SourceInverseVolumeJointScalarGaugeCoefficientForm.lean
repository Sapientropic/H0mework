import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeDoubleGramCurvatureForm
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeBrokenGaussCurvatureCurrent
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeMomentumCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceJointScalarGaugeCoefficientForm
open GaussLiveMomentum GaussCoreDifferential GaussCoreHilbert GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussNativeMatter GaussFockPair
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceElectricColumns SourceNativeMixedCurvatureReduction
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeAuxiliaryVariation
open StageNineCoframeGravityGaugeRegularity SourceQuantumResidualGaugeSlice StageNineP286LinkedActiveGaugeBFAlgebra
open scoped InnerProductSpace ContDiff
open SourceDoubleGramCurvatureForm SourceNativeMomentumCurvature
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem native_skew (a b c : NativeLie) :
    inner ℝ (SourceCartanCubic.nativeBracket a b) c+
      inner ℝ b (SourceCartanCubic.nativeBracket a c)=0 := by
  change p286CoordinateLiePairing (jointP286CoordinateLieBracket a b) c+
    p286CoordinateLiePairing b (jointP286CoordinateLieBracket a c)=0
  exact p286CoordinateLiePairing_adjoint_skew a b c

private theorem gauge_rotation_skew (r : ScalarIndex) (b a : LieIndex) (z : SourceCoordinateSlice) :
    gaugeRotation r b a z= -gaugeRotation r a b z := by
  have h := native_skew (inverseL z (scalarDirection r)).1 (lieBasis a) (lieBasis b)
  rw [real_inner_comm (lieBasis b) (SourceCartanCubic.nativeBracket (inverseL z (scalarDirection r)).1 (lieBasis a))] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem gauge_rotation_action_skew (r : ScalarIndex) (b a : LieIndex) :
    gaugeRotationAction r b a= -gaugeRotationAction r a b := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (gaugeRotation r b a z : ℂ) • f z= -((gaugeRotation r a b z : ℂ) • f z)
  rw [gauge_rotation_skew,Complex.ofReal_neg,neg_smul]

private theorem real_fock_smul (r : ℝ) (f : FockFiber) : r • f=(r : ℂ) • f := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem scalar_rotation_momentum (v : Ambient) (i : ScalarIndex) (z : SourceCoordinateSlice) (f : QuantumTest) :
    covariantMomentum (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i),0) f z=
      ∑ j : ScalarIndex,(scalarRotation v j i z : ℂ) • covariantMomentum (scalarDirection j) f z := by
  have he : (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i), (0 : Gauge))=
      ∑ j : ScalarIndex,scalarRotation v j i z • scalarDirection j := by
    apply Prod.ext
    · simpa only [Prod.fst_sum,Prod.smul_fst,scalarDirection,scalarRotation] using
        (scalarBasis.sum_repr' (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i))).symm
    · simp only [Prod.snd_sum,Prod.smul_snd,scalarDirection,smul_zero,Finset.sum_const_zero]
  have hp := congrArg (pointMomentum f z) he
  simp only [map_sum,map_smul,real_fock_smul] at hp
  change covariantMomentum (scalarP286ActionBilinear (inverseL z v).1 (scalarBasis i),0) f z=
      ∑ j : ScalarIndex,(scalarRotation v j i z : ℂ) • covariantMomentum (scalarDirection j) f z at hp
  exact hp

private def gaugeInsert (j : Fin 3) : NativeLie →ₗ[ℝ] Gauge :=
  gaugeCoordinates.symm.toLinearMap.comp (LinearMap.single ℝ (fun _ : Fin 3 => NativeLie) j)

private theorem gauge_insert_bracket (j : Fin 3) (a b : NativeLie) :
    nativeGauge a (gaugeInsert j b)=gaugeInsert j (SourceCartanCubic.nativeBracket a b) := by
  apply gaugeCoordinates.injective
  funext k
  have hg (x : NativeLie) : gaugeCoordinates (gaugeInsert j x)=Pi.single j x := by
    change gaugeCoordinates (gaugeCoordinates.symm (Pi.single j x))=_
    rw [gaugeCoordinates.apply_symm_apply]
  have hn (x : Gauge) : gaugeCoordinates (nativeGauge a x) k=
      SourceCartanCubic.nativeBracket a (gaugeCoordinates x k) := rfl
  rw [hn,hg,hg]
  by_cases h : k=j
  · subst k
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h,map_zero]

private theorem gauge_rotation_momentum (r : ScalarIndex) (j : Fin 3) (a : LieIndex)
    (z : SourceCoordinateSlice) (f : QuantumTest) :
    covariantMomentum (0,nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2) f z=
      ∑ b : LieIndex,(gaugeRotation r b a z : ℂ) • covariantMomentum (gaugeDirection j b) f z := by
  have hg : nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2=
      ∑ b : LieIndex,gaugeRotation r b a z • (gaugeDirection j b).2 := by
    change nativeGauge (inverseL z (scalarDirection r)).1 (gaugeInsert j (lieBasis a))=_
    rw [gauge_insert_bracket]
    have h := congrArg (gaugeInsert j) (lieBasis.sum_repr'
      (SourceCartanCubic.nativeBracket (inverseL z (scalarDirection r)).1 (lieBasis a)))
    simp only [map_sum,map_smul] at h
    exact h.symm
  have he : ((0,nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2) : Ambient)=
      ∑ b : LieIndex,gaugeRotation r b a z • gaugeDirection j b := by
    apply Prod.ext
    · simp only [Prod.fst_sum,Prod.smul_fst,gaugeDirection,smul_zero,Finset.sum_const_zero]
    · simpa only [Prod.snd_sum,Prod.smul_snd] using hg
  have hp := congrArg (pointMomentum f z) he
  simp only [map_sum,map_smul,real_fock_smul] at hp
  change covariantMomentum (0,nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2) f z=
      ∑ b : LieIndex,(gaugeRotation r b a z : ℂ) • covariantMomentum (gaugeDirection j b) f z at hp
  exact hp

private theorem curvature_frame (r : ScalarIndex) (j : Fin 3) (a : LieIndex) :
    curvatureRow (scalarDirection r) (gaugeDirection j a)=
      Complex.I • ∑ i : ScalarIndex,scalarRotationAction (gaugeDirection j a) i r*covariantMomentum (scalarDirection i)+
      (-Complex.I) • ∑ b : LieIndex,gaugeRotationAction r b a*covariantMomentum (gaugeDirection j b) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have h := original_scalar_gauge_curvature ⟨z,hz⟩ (scalarBasis r) (gaugeDirection j a).2 f
    have ha := scalar_rotation_momentum (gaugeDirection j a) r z f
    change covariantMomentum (scalarP286ActionBilinear (inverseL z (0,(gaugeDirection j a).2)).1 (scalarBasis r),0) f z=_ at ha
    rw [original_gauge_inverse ⟨z,hz⟩] at ha
    rw [ha] at h
    change covariantMomentum (scalarDirection r) (covariantMomentum (gaugeDirection j a) f) z-
      covariantMomentum (gaugeDirection j a) (covariantMomentum (scalarDirection r) f) z=
      (-Complex.I) • (-(∑ i : ScalarIndex,(scalarRotation (gaugeDirection j a) i r z : ℂ) • covariantMomentum (scalarDirection i) f z)+
        covariantMomentum (0,nativeGauge (inverseL z (scalarDirection r)).1 (gaugeDirection j a).2) f z) at h
    rw [gauge_rotation_momentum] at h
    simp only [curvatureRow,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.add_apply,
      LinearMap.smul_apply,LinearMap.sum_apply,add_apply,smul_apply,sum_apply,
      scalarRotationAction,gaugeRotationAction,multiply_apply]
    change covariantMomentum (scalarDirection r) (covariantMomentum (gaugeDirection j a) f) z-
      covariantMomentum (gaugeDirection j a) (covariantMomentum (scalarDirection r) f) z=_ at h
    change covariantMomentum (scalarDirection r) (covariantMomentum (gaugeDirection j a) f) z-
      covariantMomentum (gaugeDirection j a) (covariantMomentum (scalarDirection r) f) z=_
    linear_combination (norm := module) h
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem metric_derivative (z : physicalChart) (u : Ambient) (i j : Fin 3) :
    fderiv ℝ (fun x => gaugeWeight x i j) z.val (direction u z.val)=0 := by
  have hf := ((gaugeWeight_smooth i j z).differentiableAt (by simp)).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ => z.val+t • direction u z.val) (direction u z.val) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (direction u z.val)).const_add z.val
  have hd := hf.comp_hasDerivAt_of_eq 0 ht (by simp)
  have he : (fun t : ℝ => gaugeWeight (z.val+t • direction u z.val) i j)=fun _ : ℝ => gaugeWeight z.val i j := by
    funext t
    simp only [gaugeWeight,volume,inverseSpatial,direction,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
  change HasDerivAt (fun t : ℝ => gaugeWeight (z.val+t • direction u z.val) i j)
    (fderiv ℝ (fun x => gaugeWeight x i j) z.val (direction u z.val)) 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 _)

private theorem momentum_metric (u : Ambient) (i j : Fin 3) :
    Commute (covariantMomentum u) (GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · let M := GaussNativeForm.multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
    have he : (M f : SourceCoordinateSlice → FockFiber)=fun x => gaugeWeight x i j • f x := by
      funext x
      exact (real_fock_smul _ _).symm
    have hd : directional u (M f) z=(gaugeWeight z i j : ℂ) • directional u f z := by
      rw [directional_apply,he,fderiv_fun_smul ((gaugeWeight_smooth i j ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change gaugeWeight z i j • fderiv ℝ f z (direction u z)+
        fderiv ℝ (fun x => gaugeWeight x i j) z (direction u z) • f z=_
      rw [metric_derivative ⟨z,hz⟩,zero_smul,add_zero,real_fock_smul]
      rfl
    change (-Complex.I) • (directional u (M f) z+connection u z ((gaugeWeight z i j : ℂ) • f z))=
      (gaugeWeight z i j : ℂ) • ((-Complex.I) • (directional u f z+connection u z (f z)))
    rw [hd,map_smul,←smul_add,smul_comm]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem adjoint_metric (u : Ambient) (i j : Fin 3) :
    Commute (GaussMomentumAdjoint.adjoint u) (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) := by
  apply LinearMap.ext
  intro q
  apply SourceCoframeVolume.pair_ext
  intro p
  change sourcePair p (GaussMomentumAdjoint.adjoint u (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) q))=
    sourcePair p (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) (GaussMomentumAdjoint.adjoint u q))
  rw [GaussNativeForm.adjoint_pair,multiply_pair,multiply_pair,GaussNativeForm.adjoint_pair]
  exact congrArg (fun x => sourcePair x q) (LinearMap.congr_fun (momentum_metric u i j).eq.symm p)

private theorem gauge_metric_symmetric (i j : Fin 3) :
    multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)=
      multiply (fun z => gaugeWeight z j i) (gaugeWeight_smooth j i) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun c : ℝ => (c : ℂ) • f z) (gaugeWeight_symmetric z i j)

private theorem pair_sum {ι : Type} [Fintype ι] (p : QuantumTest) (q : ι → QuantumTest) : sourcePair p (∑ i,q i)=∑ i,sourcePair p (q i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem pair_smul (p q : QuantumTest) (c : ℂ) : sourcePair p (c • q)=c*sourcePair p q := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_add (p q r : QuantumTest) : sourcePair p (q+r)=sourcePair p q+sourcePair p r := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]

private def metricAction (i j : Fin 3) : End := multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)

private def scalarDensityRow (r : ScalarIndex) (j : Fin 3) (a : LieIndex) : End :=
  (∑ s : ScalarIndex,(Complex.I • scalarCoefficientCurrent (gaugeDirection j a) s r+
      divergenceAction (scalarDirection r)*scalarRotationAction (gaugeDirection j a) s r)*covariantMomentum (scalarDirection s))+
  densityContact (gaugeDirection j a) (scalarDirection r)*covariantMomentum (scalarDirection r)

private def negativeGaugeRow (r : ScalarIndex) (j : Fin 3) (a : LieIndex) : End :=
  ∑ b : LieIndex,((-Complex.I) • gaugeCoefficientCurrent r b a-
      divergenceAction (scalarDirection r)*gaugeRotationAction r b a)*covariantMomentum (gaugeDirection j b)

private theorem lower_row_split (r : ScalarIndex) (j : Fin 3) (a : LieIndex) :
    scalarGaugeLowerRow r j a=scalarDensityRow r j a+negativeGaugeRow r j a := by
  unfold scalarGaugeLowerRow scalarDensityRow negativeGaugeRow
  abel

private theorem contact_coefficient (r : ScalarIndex) (i j : Fin 3) (a b : LieIndex) :
    metricAction i j*(((-Complex.I) • gaugeCoefficientCurrent r b a-
      divergenceAction (scalarDirection r)*gaugeRotationAction r b a))=
      (-Complex.I) • weightedGaugeContact r (i,a) (j,b) := by
  have hw : weightedGaugeRotation r (i,a) (j,b)=metricAction i j*gaugeRotationAction r b a := by
    apply LinearMap.ext
    intro q
    apply DFunLike.ext
    intro z
    change ((gaugeWeight z i j*gaugeRotation r b a z : ℝ) : ℂ) • q z=
      (gaugeWeight z i j : ℂ) • ((gaugeRotation r b a z : ℂ) • q z)
    rw [smul_smul,Complex.ofReal_mul]
  have ha : GaussMomentumAdjoint.adjoint (scalarDirection r)*metricAction i j=
      metricAction i j*GaussMomentumAdjoint.adjoint (scalarDirection r) := (adjoint_metric _ i j).eq
  rw [weightedGaugeContact,hw,←mul_assoc,ha,mul_assoc,original_adjoint_divergence]
  unfold gaugeCoefficientCurrent
  simp only [sub_mul,smul_mul_assoc,mul_sub,mul_smul_comm,mul_assoc]
  simp only [smul_sub,smul_smul]
  have hI : (Complex.I*Complex.I) • (metricAction i j*(divergenceAction (scalarDirection r)*gaugeRotationAction r b a))=
      -(metricAction i j*(divergenceAction (scalarDirection r)*gaugeRotationAction r b a)) := by
    rw [Complex.I_mul_I,neg_one_smul]
  linear_combination (norm := module) -hI

private def scalarDensityPair (f : QuantumTest) : ℂ := ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,∑ r : ScalarIndex,
  sourcePair (covariantMomentum (gaugeDirection i a) f) (metricAction i j (scalarDensityRow r j a f))

private theorem negative_gauge_contact_cancel (f : QuantumTest) :
    lowerGaugePair f=scalarDensityPair f+(-Complex.I)*(∑ r : ScalarIndex,gaugeContactPair r f) := by
  simp only [lowerGaugePair,lower_row_split,LinearMap.add_apply,map_add,pair_add,Finset.sum_add_distrib,
    negativeGaugeRow,LinearMap.sum_apply,Module.End.mul_apply,map_sum,pair_sum,scalarDensityPair,metricAction]
  congr 1
  have hterm (a : LieIndex) (i j : Fin 3) (r : ScalarIndex) (b : LieIndex) :
      sourcePair (covariantMomentum (gaugeDirection i a) f)
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
          (((-Complex.I) • gaugeCoefficientCurrent r b a-divergenceAction (scalarDirection r)*gaugeRotationAction r b a)
            (covariantMomentum (gaugeDirection j b) f)))=
      (-Complex.I)*sourcePair (gaugeMomentum (i,a) f)
        (weightedGaugeContact r (i,a) (j,b) (gaugeMomentum (j,b) f)) := by
    have h := LinearMap.congr_fun (contact_coefficient r i j a b) (covariantMomentum (gaugeDirection j b) f)
    simpa only [metricAction,Module.End.mul_apply,LinearMap.smul_apply,pair_smul,gaugeMomentum] using congrArg (sourcePair (covariantMomentum (gaugeDirection i a) f)) h
  simp only [hterm,←Finset.mul_sum]
  congr 1
  rw [show (∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,∑ r : ScalarIndex,∑ b : LieIndex,
      sourcePair (gaugeMomentum (i,a) f) (weightedGaugeContact r (i,a) (j,b) (gaugeMomentum (j,b) f)))=
      ∑ r : ScalarIndex,∑ i : Fin 3,∑ a : LieIndex,∑ j : Fin 3,∑ b : LieIndex,
        sourcePair (gaugeMomentum (i,a) f) (weightedGaugeContact r (i,a) (j,b) (gaugeMomentum (j,b) f)) from by
    rw [show (∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,∑ r : ScalarIndex,∑ b : LieIndex,
      sourcePair (gaugeMomentum (i,a) f) (weightedGaugeContact r (i,a) (j,b) (gaugeMomentum (j,b) f)))=
      ∑ a : LieIndex,∑ i : Fin 3,∑ r : ScalarIndex,∑ j : Fin 3,∑ b : LieIndex,
        sourcePair (gaugeMomentum (i,a) f) (weightedGaugeContact r (i,a) (j,b) (gaugeMomentum (j,b) f)) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm),Finset.sum_comm]
    exact Finset.sum_congr rfl (fun r _ => Finset.sum_comm)]
  simp only [gaugeContactPair,Fintype.sum_prod_type]

private def gaugeSquareAction (r : ScalarIndex) (i j : GaugeRow) (b : LieIndex) : End :=
  metricAction i.1 j.1*gaugeRotationAction r b i.2*gaugeRotationAction r j.2 b

private theorem gauge_square_action_symmetric (r : ScalarIndex) (i j : GaugeRow) (b : LieIndex) :
    gaugeSquareAction r i j b=gaugeSquareAction r j i b := by
  apply LinearMap.ext
  intro q
  apply DFunLike.ext
  intro z
  change (gaugeWeight z i.1 j.1 : ℂ) • ((gaugeRotation r b i.2 z : ℂ) • ((gaugeRotation r j.2 b z : ℂ) • q z))=
    (gaugeWeight z j.1 i.1 : ℂ) • ((gaugeRotation r b j.2 z : ℂ) • ((gaugeRotation r i.2 b z : ℂ) • q z))
  rw [gaugeWeight_symmetric z j.1 i.1,gauge_rotation_skew r b j.2,gauge_rotation_skew r i.2 b]
  simp only [Complex.ofReal_neg,smul_smul,mul_neg,neg_mul,neg_neg]
  congr 1
  ring

private theorem gauge_square_pair (r : ScalarIndex) (i j : GaugeRow) (b : LieIndex) (p q : QuantumTest) :
    sourcePair p (gaugeSquareAction r i j b q)=sourcePair (gaugeSquareAction r i j b p) q := by
  change sourcePair p (metricAction i.1 j.1 (gaugeRotationAction r b i.2 (gaugeRotationAction r j.2 b q)))=_
  change sourcePair p (multiply _ _ (multiply _ _ (multiply _ _ q)))=_
  rw [multiply_pair,multiply_pair,multiply_pair]
  congr 1
  apply DFunLike.ext
  intro z
  change (gaugeRotation r j.2 b z : ℂ) • ((gaugeRotation r b i.2 z : ℂ) • ((gaugeWeight z i.1 j.1 : ℂ) • p z))=
    (gaugeWeight z i.1 j.1 : ℂ) • ((gaugeRotation r b i.2 z : ℂ) • ((gaugeRotation r j.2 b z : ℂ) • p z))
  simp only [smul_smul]
  congr 1
  ring

private def gaugeSquarePair (r : ScalarIndex) (f : QuantumTest) : ℂ := ∑ i : GaugeRow,∑ j : GaugeRow,∑ b : LieIndex,
  sourcePair (gaugeMomentum i f) (gaugeSquareAction r i j b (gaugeMomentum j f))

private theorem gauge_square_pair_real (r : ScalarIndex) (f : QuantumTest) : (gaugeSquarePair r f).im=0 := by
  have h : star (gaugeSquarePair r f)=gaugeSquarePair r f := by
    simp only [gaugeSquarePair,star_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro b _
    change (starRingEnd ℂ) (sourcePair (gaugeMomentum j f) (gaugeSquareAction r j i b (gaugeMomentum i f)))=_
    rw [pair_conjugate,←gauge_square_pair,gauge_square_action_symmetric]
  have hh := congrArg Complex.im h
  simp only [Complex.star_def,Complex.conj_im] at hh
  linarith

private def scalarCurvatureRow (r : ScalarIndex) (j : Fin 3) (a : LieIndex) : End := ∑ b : LieIndex,∑ s : ScalarIndex,
  gaugeRotationAction r b a*scalarRotationAction (gaugeDirection j b) s r*covariantMomentum (scalarDirection s)

private def scalarCurvaturePair (r : ScalarIndex) (f : QuantumTest) : ℂ := ∑ i : GaugeRow,∑ j : Fin 3,
  sourcePair (gaugeMomentum i f) (metricAction i.1 j (scalarCurvatureRow r j i.2 f))

private theorem gauge_curvature_pair_split (r : ScalarIndex) (f : QuantumTest) :
    gaugeCurvaturePair r f=Complex.I*scalarCurvaturePair r f+(-Complex.I)*gaugeSquarePair r f := by
  simp only [gaugeCurvaturePair,curvature_frame,LinearMap.add_apply,LinearMap.smul_apply,
    LinearMap.sum_apply,Module.End.mul_apply,map_add,map_smul,map_sum,pair_add,pair_smul,pair_sum,
    Finset.sum_add_distrib,←Finset.mul_sum,scalarCurvaturePair,scalarCurvatureRow,gaugeSquarePair,gaugeSquareAction]
  apply congrArg₂ (fun x y : ℂ => x+y)
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    apply DFunLike.ext
    intro z
    change ((gaugeWeight z i.1 j*gaugeRotation r b i.2 z : ℝ) : ℂ) •
      ((scalarRotation (gaugeDirection j b) s r z : ℂ) • covariantMomentum (scalarDirection s) f z)=
      (gaugeWeight z i.1 j : ℂ) • ((gaugeRotation r b i.2 z : ℂ) •
        ((scalarRotation (gaugeDirection j b) s r z : ℂ) • covariantMomentum (scalarDirection s) f z))
    simp only [smul_smul,Complex.ofReal_mul,mul_assoc]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply DFunLike.ext
    intro z
    change ((gaugeWeight z i.1 j*gaugeRotation r b i.2 z : ℝ) : ℂ) •
      ((gaugeRotation r c b z : ℂ) • covariantMomentum (gaugeDirection j c) f z)=
      (gaugeWeight z i.1 j : ℂ) • ((gaugeRotation r b i.2 z : ℂ) •
        ((gaugeRotation r c b z : ℂ) • covariantMomentum (gaugeDirection j c) f z))
    simp only [smul_smul,Complex.ofReal_mul,mul_assoc]

open GaussScalarTransport GaussDensityCore

private theorem real_multiplier_current (u : Ambient) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) (z : physicalChart) :
    covariantMomentum u (multiply c hc f) z.val-multiply c hc (covariantMomentum u f) z.val=
      (-Complex.I) • ((fderiv ℝ c z.val (direction u z.val) : ℂ) • f z.val) := by
  have he : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
    funext x
    exact (real_fock_smul _ _).symm
  have hd : directional u (multiply c hc f) z.val=(c z.val : ℂ) • directional u f z.val+
      (fderiv ℝ c z.val (direction u z.val) : ℂ) • f z.val := by
    rw [directional_apply,he,fderiv_fun_smul ((hc z).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt]
    change c z.val • fderiv ℝ f z.val (direction u z.val)+fderiv ℝ c z.val (direction u z.val) • f z.val=_
    rw [real_fock_smul,real_fock_smul]
    rfl
  change (-Complex.I) • (directional u (multiply c hc f) z.val+connection u z.val ((c z.val : ℂ) • f z.val))-
    (c z.val : ℂ) • ((-Complex.I) • (directional u f z.val+connection u z.val (f z.val)))=_
  rw [hd,map_smul]
  module

private theorem coefficient_density_smooth (N : ℕ) (v : Ambient) (i : FrameIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val :=
  (complexDensity_smooth N z).mul (coefficient_smooth v i z)

private theorem field_transpose_value (N : ℕ) (v : Ambient) (f : ScalarTest) (z : physicalChart) :
    fieldTranspose N v f z.val=
      -fieldDerivative v f z.val-divergenceCoefficient N v z.val*f z.val := by
  have hr : complexDensity N z.val≠0 := by
    change (density N z.val : ℂ)≠0
    exact_mod_cast (density_pos N z).ne'
  have hterm (i : FrameIndex) :
      weightedTranspose N (frame i) (multiplyCoefficient v i f) z.val=
        -(coefficient v i z.val : ℂ)*derivative (frame i) f z.val-
          ((complexDensity N z.val)⁻¹*fderiv ℝ
            (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val (frame i))*f z.val := by
    rw [weightedTranspose_apply]
    have he : (fun x => complexDensity N x*(multiplyCoefficient v i f) x)=
        fun x => (complexDensity N x*(coefficient v i x : ℂ))*f x := by
      funext x
      change complexDensity N x*((coefficient v i x : ℂ)*f x)=(complexDensity N x*(coefficient v i x : ℂ))*f x
      ring
    rw [he,fderiv_fun_mul ((coefficient_density_smooth N v i z).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt,derivative_apply]
    change -(complexDensity N z.val)⁻¹*
      ((complexDensity N z.val*(coefficient v i z.val : ℂ))*fderiv ℝ f z.val (frame i)+
        f z.val*fderiv ℝ (fun x => complexDensity N x*(coefficient v i x : ℂ)) z.val (frame i))=_
    field_simp [hr]
    ring
  simp only [fieldTranspose,fieldDerivative,LinearMap.sum_apply,LinearMap.comp_apply,sum_apply,
    hterm,divergenceCoefficient,Finset.sum_sub_distrib,Finset.sum_mul,neg_mul,Finset.sum_neg_distrib]
  rfl

private theorem derivative_transpose_component (v : Ambient) (f : QuantumTest) (word : Occupation) (z : physicalChart) :
    GaussMomentumAdjoint.derivativeTranspose v f z.val word=
      fieldTranspose word.card v (component word f) z.val := by
  have h := congrArg (fun x : H => x word) (GaussMomentumAdjoint.transpose_embed v f)
  change embed (GaussMomentumAdjoint.derivativeTranspose v f) word=
    scalarLp word.card (fieldTranspose word.card v (component word f)) at h
  have he : (fun x : physicalChart => GaussMomentumAdjoint.derivativeTranspose v f x.val word)=ᵐ[GaussHistoryHilbert.numberMeasure word.card]
      (fun x : physicalChart => fieldTranspose word.card v (component word f) x.val) :=
    (embed_ae (GaussMomentumAdjoint.derivativeTranspose v f) word).symm.trans
      (h.symm ▸ scalarLp_ae word.card (fieldTranspose word.card v (component word f)))
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq he
    ((component word (GaussMomentumAdjoint.derivativeTranspose v f)).continuous.comp continuous_subtype_val)
    ((fieldTranspose word.card v (component word f)).continuous.comp continuous_subtype_val)) z

private theorem divergence_value (v : Ambient) (f : QuantumTest) (z : physicalChart) :
    divergenceAction v f z.val=
      GaussFockWeights.weight (fun N => divergenceCoefficient N v z.val) (f z.val) := by
  apply PiLp.ext
  intro word
  change -(GaussMomentumAdjoint.derivativeTranspose v f z.val word+directional v f z.val word)=_
  rw [derivative_transpose_component,field_transpose_value]
  have hd := congrArg (fun q : ScalarTest => q z.val) (GaussMomentumAdjoint.component_directional v f word)
  change directional v f z.val word=fieldDerivative v (component word f) z.val at hd
  rw [hd,GaussFockWeights.weight_apply]
  change -(-fieldDerivative v (component word f) z.val-
    divergenceCoefficient word.card v z.val*f z.val word+fieldDerivative v (component word f) z.val)=_
  ring

private theorem positive_coefficient_value (u : Ambient) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (q : QuantumTest) (z : physicalChart) :
    ((Complex.I • (covariantMomentum u*multiply c hc-multiply c hc*covariantMomentum u)+
      divergenceAction u*multiply c hc) q) z.val=
      GaussFockWeights.weight (fun N => (fderiv ℝ c z.val (direction u z.val) : ℂ)+
        divergenceCoefficient N u z.val*(c z.val : ℂ)) (q z.val) := by
  change Complex.I • (covariantMomentum u (multiply c hc q) z.val-multiply c hc (covariantMomentum u q) z.val)+
    divergenceAction u (multiply c hc q) z.val=_
  rw [real_multiplier_current,divergence_value,multiply_apply,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul,map_smul]
  apply PiLp.ext
  intro word
  change (fderiv ℝ c z.val (direction u z.val) : ℂ)*q z.val word+
    (c z.val : ℂ)*(divergenceCoefficient word.card u z.val*q z.val word)=
      ((fderiv ℝ c z.val (direction u z.val) : ℂ)+divergenceCoefficient word.card u z.val*(c z.val : ℂ))*q z.val word
  ring

private theorem density_contact_value (u v : Ambient) (q : QuantumTest) (z : physicalChart) :
    densityContact u v q z.val=GaussFockWeights.weight
      (fun N => fderiv ℝ (divergenceCoefficient N v) z.val (direction u z.val)) (q z.val) := by
  change (covariantMomentum u (covariantMomentum v q) z.val-covariantMomentum v (covariantMomentum u q) z.val)-
    (covariantMomentum u (GaussMomentumAdjoint.adjoint v q) z.val-GaussMomentumAdjoint.adjoint v (covariantMomentum u q) z.val)=_
  rw [original_native_momentum_curvature,original_native_adjoint_curvature]
  module


/-- One joint row with only scalar momenta; every coefficient comes from the original inverse chart and true density. -/
def jointScalarGaugeRow (j : Fin 3) (a : LieIndex) : End := ∑ r : ScalarIndex,
  (scalarDensityRow r j a-scalarCurvatureRow r j a)

def jointScalarGaugePair (f : QuantumTest) : ℂ := ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
  sourcePair (covariantMomentum (gaugeDirection i a) f) (metricAction i j (jointScalarGaugeRow j a f))

def jointScalarGaugeForm (f : QuantumTest) : ℝ := (jointScalarGaugePair f).im/2

private theorem shuffle {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (h : A → B → C → D → ℂ) :
    (∑ a : A,∑ b : B,∑ c : C,∑ d : D,h a b c d)=
      ∑ d : D,∑ b : B,∑ a : A,∑ c : C,h a b c d := by
  calc
    _ = ∑ a : A,∑ b : B,∑ d : D,∑ c : C,h a b c d :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))
    _ = ∑ a : A,∑ d : D,∑ b : B,∑ c : C,h a b c d := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ d : D,∑ a : A,∑ b : B,∑ c : C,h a b c d := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun d _ => Finset.sum_comm)

private theorem joint_pair_split (f : QuantumTest) :
    jointScalarGaugePair f=scalarDensityPair f-∑ r : ScalarIndex,scalarCurvaturePair r f := by
  simp only [jointScalarGaugePair,jointScalarGaugeRow,LinearMap.sum_apply,LinearMap.sub_apply,
    map_sum,map_sub,pair_sum,pair_sub,Finset.sum_sub_distrib,scalarDensityPair]
  congr 1
  rw [shuffle]
  simp only [scalarCurvaturePair,Fintype.sum_prod_type,gaugeMomentum]

/-- The complete signed mixed energy has no gauge-gauge remainder or separate derivative-contact price. -/
theorem original_mixed_joint_scalar_gauge_form (f : QuantumTest) :
    mixedEnergyForm f=jointScalarGaugeForm f := by
  rw [mixedEnergyForm,negative_gauge_contact_cancel]
  simp only [gauge_curvature_pair_split,Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.I_re,
    Complex.I_im,Complex.neg_im,zero_mul,one_mul,neg_mul,gauge_square_pair_real,sub_zero,
    Complex.add_im,Complex.mul_im,zero_add,Complex.re_sum,Complex.im_sum,
    jointScalarGaugeForm,joint_pair_split,Complex.sub_im]
  simp only [neg_zero,add_zero,zero_sub,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceHamiltonianVolume
/-- The original mixed44 current consumes the same joint form at its original inverse-volume test. -/
theorem original_mixed44_joint_scalar_gauge_form (f : QuantumTest) :
    (sourcePair f (((44 : ℂ) • (inverseVolumeAction*(scalarKinetic*gaugeKinetic-gaugeKinetic*scalarKinetic))) f)).im/2=
      -22*sourceTime 0*jointScalarGaugeForm (inverseVolumeAction f) := by
  rw [original_mixed_bulk_energy_form,original_mixed_joint_scalar_gauge_form]

/-- Original Number-weighted coefficient; the native density trace remains in this joint mouth. -/
def jointCoefficient (N : ℕ) (j : Fin 3) (a : LieIndex) (s : ScalarIndex) (z : SourceCoordinateSlice) : ℂ :=
  (∑ r : ScalarIndex, (
    (fderiv ℝ (scalarRotation (gaugeDirection j a) s r) z (direction (scalarDirection r) z) : ℂ)+
    divergenceCoefficient N (scalarDirection r) z*(scalarRotation (gaugeDirection j a) s r z : ℂ)-
    ∑ b : LieIndex,(gaugeRotation r b a z : ℂ)*(scalarRotation (gaugeDirection j b) s r z : ℂ)))+
  fderiv ℝ (divergenceCoefficient N (scalarDirection s)) z (direction (gaugeDirection j a) z)

private theorem scalar_density_row_value (r : ScalarIndex) (j : Fin 3) (a : LieIndex) (f : QuantumTest) (z : physicalChart) :
    scalarDensityRow r j a f z.val=
      (∑ s : ScalarIndex,GaussFockWeights.weight (fun N =>
        (fderiv ℝ (scalarRotation (gaugeDirection j a) s r) z.val (direction (scalarDirection r) z.val) : ℂ)+
          divergenceCoefficient N (scalarDirection r) z.val*(scalarRotation (gaugeDirection j a) s r z.val : ℂ))
            (covariantMomentum (scalarDirection s) f z.val))+
      GaussFockWeights.weight (fun N => fderiv ℝ (divergenceCoefficient N (scalarDirection r)) z.val
        (direction (gaugeDirection j a) z.val)) (covariantMomentum (scalarDirection r) f z.val) := by
  simp only [scalarDensityRow,LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,add_apply,sum_apply]
  apply congrArg₂ (fun x y : FockFiber => x+y)
  · apply Finset.sum_congr rfl
    intro s _
    exact positive_coefficient_value (scalarDirection r) _ _ _ z
  · exact density_contact_value (gaugeDirection j a) (scalarDirection r) _ z

private theorem joint_component_sum {R B : Type} [Fintype R] [Fintype B]
    (A : R → R → ℂ) (T : R → B → R → ℂ) (x d : R → ℂ) :
    (∑ r : R, ((∑ s : R,A r s*x s)+d r*x r-∑ b : B,∑ s : R,T r b s*x s))=
      ∑ s : R,((∑ r : R,(A r s-∑ b : B,T r b s))+d s)*x s := by
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,add_mul,sub_mul,Finset.sum_mul]
  have ha : (∑ r : R,∑ s : R,A r s*x s)=∑ s : R,∑ r : R,A r s*x s := Finset.sum_comm
  have ht : (∑ r : R,∑ b : B,∑ s : R,T r b s*x s)=∑ s : R,∑ r : R,∑ b : B,T r b s*x s := by
    rw [Finset.sum_congr rfl (fun r _ => Finset.sum_comm),Finset.sum_comm]
  rw [ha,ht]
  abel

/-- Exact scalar-only point value of the complete joint coefficient. -/
theorem original_joint_scalar_gauge_row (j : Fin 3) (a : LieIndex) (f : QuantumTest) (z : physicalChart) :
    jointScalarGaugeRow j a f z.val=∑ s : ScalarIndex,
      GaussFockWeights.weight (fun N => jointCoefficient N j a s z.val)
        (covariantMomentum (scalarDirection s) f z.val) := by
  simp only [jointScalarGaugeRow,LinearMap.sum_apply,LinearMap.sub_apply,sum_apply,sub_apply,scalar_density_row_value]
  apply PiLp.ext
  intro word
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_sub,WithLp.ofLp_add,GaussFockWeights.weight_apply]
  simp only [scalarCurvatureRow,LinearMap.sum_apply,Module.End.mul_apply,sum_apply,gaugeRotationAction,scalarRotationAction,multiply_apply,
    WithLp.ofLp_sum,WithLp.ofLp_smul,jointCoefficient]
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,GaussFockWeights.weight_apply]
  simpa only [mul_assoc] using joint_component_sum
    (fun r s => (fderiv ℝ (scalarRotation (gaugeDirection j a) s r) z.val (direction (scalarDirection r) z.val) : ℂ)+
      divergenceCoefficient word.card (scalarDirection r) z.val*(scalarRotation (gaugeDirection j a) s r z.val : ℂ))
    (fun r b s => (gaugeRotation r b a z.val : ℂ)*(scalarRotation (gaugeDirection j b) s r z.val : ℂ))
    (fun s => covariantMomentum (scalarDirection s) f z.val word)
    (fun s => fderiv ℝ (divergenceCoefficient word.card (scalarDirection s)) z.val (direction (gaugeDirection j a) z.val))

end LowEnergy.SourceJointScalarGaugeCoefficientForm
