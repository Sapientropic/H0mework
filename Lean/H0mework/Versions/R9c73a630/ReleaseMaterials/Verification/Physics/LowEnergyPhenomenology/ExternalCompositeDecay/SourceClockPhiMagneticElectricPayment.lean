import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWeightedElectricSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.FirstCurrentGeometricPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare
open SourceClockPhiMatchedElectricSource SourceCoframeVolume SourceCornerWeight SourceCartanCubic
open SourceQuantumGaugeCenterMagnetic SourceScalarVirialBulk SourceClockPhiNativeMatchedSource SourceScalarDoubleCurrent
open SaturationMonoid.PhysicsCore.StageNineP286BracketCalculus
open scoped InnerProductSpace RealInnerProductSpace ContDiff Matrix
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev W : End := magneticVolumeWeight
private abbrev P : End := electricPrimitive
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem sigma_pos:0<sourceSigma:=
  SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource.legacy.sigma_pos
private theorem electric_smooth(z:physicalChart):ContDiffAt ℝ ∞ electricWeight z.val:=
  (reciprocal_volume_smooth z).mul (SourceGaugeRadialCurrent.electric_square_smooth z)
private theorem electric_formula(z:SourceCoordinateSlice):electricWeight z=
    n/(sourceSigma*(volume z)^2)*gaugeSquare z:=by
  unfold electricWeight SourceGaugeRadiusMetric.electricSquare reciprocalVolume
  ring
private def rowTangent(i:Fin 6)(z:SourceCoordinateSlice)(j:Fin 3):NativeLie:=
  !![connectionField z 0,0,0;
    0,connectionField z 0,0;
    0,connectionField z 1,0;
    0,0,connectionField z 0;
    0,0,connectionField z 1;
    0,0,connectionField z 2] i j
private def squareGradient(i:Fin 6)(z:SourceCoordinateSlice):ℝ:=
  2*∑j:Fin 3,inner ℝ (gaugeRow z j) (rowTangent i z j)
private theorem connection_coframe_line(z:SourceCoordinateSlice)(i:Fin 6)(t:ℝ)(j:Fin 3):
    connectionField (z+t • GaussCoframeCore.coframeDirection i) j=connectionField z j:=by
  simp only [connectionField,GaussCoframeCore.coframeDirection,Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]
attribute [local irreducible] connectionField
private def threeRow {V:Type*}[AddCommGroup V][Module ℝ V]
    (q:Fin 6 → ℝ)(A:Fin 3 → V)(j:Fin 3):V:=
  ![q 0 • A 0,q 1 • A 0+q 2 • A 1,q 3 • A 0+q 4 • A 1+q 5 • A 2] j
private def threeTangent {V:Type*}[AddCommGroup V][Module ℝ V]
    (A:Fin 3 → V)(i:Fin 6)(j:Fin 3):V:=
  !![A 0,0,0;0,A 0,0;0,A 1,0;0,0,A 0;0,0,A 1;0,0,A 2] i j
private theorem three_row_line{V:Type*}[AddCommGroup V][Module ℝ V]
    (q:Fin 6 → ℝ)(A:Fin 3 → V)(i:Fin 6)(j:Fin 3)(t:ℝ):
    threeRow (fun k=>q k+t*(if i=k then 1 else 0)) A j=threeRow q A j+t • threeTangent A i j:=by
  fin_cases i <;> fin_cases j <;>
    simp [threeRow,threeTangent,add_smul,add_assoc,add_comm,add_left_comm]
private theorem row_line(i:Fin 6)(j:Fin 3)(z:SourceCoordinateSlice)(t:ℝ):
    gaugeRow (z+t • GaussCoframeCore.coframeDirection i) j=
      gaugeRow z j+t • rowTangent i z j := by
  have hq(k:Fin 6):(z+t • GaussCoframeCore.coframeDirection i).1 k=
      z.1 k+t*(if i=k then 1 else 0):=by
    simp [GaussCoframeCore.coframeDirection,EuclideanSpace.single,eq_comm]
  have h:=three_row_line (fun k=>z.1 k) (connectionField z) i j t
  simpa only [threeRow,threeTangent,gaugeRow,connection_coframe_line,hq,rowTangent] using h
private theorem square_line_derivative(z:SourceCoordinateSlice)(i:Fin 6):
    HasDerivAt (fun t:ℝ=>gaugeSquare (z+t • GaussCoframeCore.coframeDirection i)) (squareGradient i z) 0 := by
  have h(j:Fin 3):HasDerivAt (fun t:ℝ=>gaugeRow (z+t • GaussCoframeCore.coframeDirection i) j)
      (rowTangent i z j) 0:=by
    simpa only [row_line,one_smul,id_eq] using!
      ((hasDerivAt_id (0:ℝ)).smul_const (rowTangent i z j)).const_add (gaugeRow z j)
  have hj(j:Fin 3):HasDerivAt
      (fun t:ℝ=>inner ℝ (gaugeRow (z+t • GaussCoframeCore.coframeDirection i) j)
        (gaugeRow (z+t • GaussCoframeCore.coframeDirection i) j))
      (2*inner ℝ (gaugeRow z j) (rowTangent i z j)) 0:=by
    have ht:inner ℝ (gaugeRow z j) (rowTangent i z j)+
        inner ℝ (rowTangent i z j) (gaugeRow z j)=2*inner ℝ (gaugeRow z j) (rowTangent i z j):=by
      rw [real_inner_comm (gaugeRow z j) (rowTangent i z j)]
      ring
    simpa only [zero_smul,add_zero,ht] using! (h j).inner ℝ (h j)
  simpa only [gaugeSquare,squareGradient,Finset.mul_sum,Finset.sum_apply] using!
    (HasDerivAt.sum (u:=Finset.univ) (fun j _=>hj j))
private def electricCoframeGradient(i:Fin 6)(z:SourceCoordinateSlice):ℝ:=
  n/(sourceSigma*(volume z)^3)*(volume z*squareGradient i z-2*gaugeSquare z*volumeGradient z i)
private theorem electric_coframe_derivative(z:physicalChart)(i:Fin 6):
    fderiv ℝ electricWeight z.val (GaussCoframeCore.coframeDirection i)=electricCoframeGradient i z.val := by
  have hl:HasDerivAt (fun t:ℝ=>z.val+t • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0:=by
    simpa only [one_smul,id_eq] using!
      ((hasDerivAt_id (0:ℝ)).smul_const (GaussCoframeCore.coframeDirection i)).const_add z.val
  have hv:=((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val))
    |>.comp_hasDerivAt_of_eq 0 hl (by simp)
  have he:=((electric_smooth z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hV:HasDerivAt (fun t:ℝ=>volume (z.val+t • GaussCoframeCore.coframeDirection i))
      (volumeGradient z.val i) 0:=by
    simpa only [Function.comp_def,volume_coordinate_derivative] using! hv
  have hh:=((hasDerivAt_const (0:ℝ) n).div ((hV.pow 2).const_mul sourceSigma)
    (by simpa only [Pi.pow_apply,zero_smul,add_zero] using mul_ne_zero source_sigma_nonzero (pow_ne_zero 2 (volume_pos z).ne'))).mul
      (square_line_derivative z.val i)
  have he':HasDerivAt (fun t:ℝ=>electricWeight (z.val+t • GaussCoframeCore.coframeDirection i))
      (fderiv ℝ electricWeight z.val (GaussCoframeCore.coframeDirection i)) 0:=by
    simpa only [Function.comp_def] using! he
  simp_rw [electric_formula] at he'
  have hd:=he'.unique hh
  simp only [Pi.pow_apply,Pi.div_apply,zero_smul,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one] at hd
  rw [hd,electricCoframeGradient]
  field_simp [(volume_pos z).ne',source_sigma_nonzero]
  ring
private def wedgePolynomial(z:SourceCoordinateSlice):ℝ:=
  (gaugeSquare z)^2-∑i:Fin 3,∑j:Fin 3,(inner ℝ (gaugeRow z i) (gaugeRow z j))^2
private theorem wedge_nonnegative(z:SourceCoordinateSlice):0≤wedgePolynomial z := by
  have h:∀i j:Fin 3,(inner ℝ (gaugeRow z i) (gaugeRow z j))^2≤
      inner ℝ (gaugeRow z i) (gaugeRow z i)*inner ℝ (gaugeRow z j) (gaugeRow z j):=by
    intro i j
    simpa only [pow_two] using real_inner_mul_inner_self_le (gaugeRow z i) (gaugeRow z j)
  have hh:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>
    Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>h i j))
  unfold wedgePolynomial
  apply sub_nonneg.mpr
  simpa only [gaugeSquare,pow_two,Finset.sum_mul,Finset.mul_sum,mul_comm] using hh
private def gaugeGram(z:SourceCoordinateSlice)(i j:Fin 3):ℝ:=inner ℝ (connectionField z i) (connectionField z j)
private def squarePoly(q:Coframe)(G:Fin 3 → Fin 3 → ℝ):ℝ:=
  q 0^2*G 0 0+q 1^2*G 0 0+2*q 1*q 2*G 0 1+q 2^2*G 1 1+
  q 3^2*G 0 0+2*q 3*q 4*G 0 1+2*q 3*q 5*G 0 2+q 4^2*G 1 1+2*q 4*q 5*G 1 2+q 5^2*G 2 2
private def gradientPoly(q:Coframe)(G:Fin 3 → Fin 3 → ℝ):Fin 6 → ℝ:=
  ![2*q 0*G 0 0,2*q 1*G 0 0+2*q 2*G 0 1,2*q 1*G 0 1+2*q 2*G 1 1,
    2*q 3*G 0 0+2*q 4*G 0 1+2*q 5*G 0 2,
    2*q 3*G 0 1+2*q 4*G 1 1+2*q 5*G 1 2,
    2*q 3*G 0 2+2*q 4*G 1 2+2*q 5*G 2 2]
private def wedgePoly(q:Coframe)(G:Fin 3 → Fin 3 → ℝ):ℝ:=
  squarePoly q G^2-((q 0^2*G 0 0)^2+
    (q 1^2*G 0 0+2*q 1*q 2*G 0 1+q 2^2*G 1 1)^2+
    (q 3^2*G 0 0+2*q 3*q 4*G 0 1+2*q 3*q 5*G 0 2+q 4^2*G 1 1+2*q 4*q 5*G 1 2+q 5^2*G 2 2)^2+
    2*(q 0*(q 1*G 0 0+q 2*G 0 1))^2+
    2*(q 0*(q 3*G 0 0+q 4*G 0 1+q 5*G 0 2))^2+
    2*(q 1*q 3*G 0 0+(q 1*q 4+q 2*q 3)*G 0 1+q 1*q 5*G 0 2+q 2*q 4*G 1 1+q 2*q 5*G 1 2)^2)
private theorem square_poly(z:SourceCoordinateSlice):gaugeSquare z=squarePoly z.1 (gaugeGram z) := by
  simp only [gaugeSquare,gaugeRow,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm (connectionField z 0) (connectionField z 1),
    real_inner_comm (connectionField z 0) (connectionField z 2),real_inner_comm (connectionField z 1) (connectionField z 2)]
  unfold squarePoly gaugeGram
  ring
private theorem square_gradient_poly(z:SourceCoordinateSlice)(i:Fin 6):squareGradient i z=gradientPoly z.1 (gaugeGram z) i := by
  fin_cases i <;>
    simp [squareGradient,rowTangent,gaugeRow,gradientPoly,gaugeGram,Fin.sum_univ_three,
      inner_add_right,real_inner_smul_right,real_inner_comm] <;> ring
private theorem wedge_poly(z:SourceCoordinateSlice):wedgePolynomial z=wedgePoly z.1 (gaugeGram z) := by
  rw [wedgePolynomial,square_poly]
  simp only [gaugeRow,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm (connectionField z 0) (connectionField z 1),
    real_inner_comm (connectionField z 0) (connectionField z 2),real_inner_comm (connectionField z 1) (connectionField z 2)]
  unfold wedgePoly gaugeGram
  ring
private theorem scalar_contact_polynomial(q:Coframe)(G:Fin 3 → Fin 3 → ℝ):
    (∑i:Fin 6,∑j:Fin 6,((q 0*q 2*q 5)*gradientPoly q G i-2*squarePoly q G*(![q 2*q 5,0,q 0*q 5,0,0,q 0*q 2]:Fin 6 → ℝ) i)*
      (GaussCoframeKinetic.polynomial q i j*((q 0*q 2*q 5)*gradientPoly q G j-2*squarePoly q G*(![q 2*q 5,0,q 0*q 5,0,0,q 0*q 2]:Fin 6 → ℝ) j)))=
      8*(q 0*q 2*q 5)^2*wedgePoly q G := by
  simp [gradientPoly,squarePoly,wedgePoly,GaussCoframeKinetic.polynomial,Fin.sum_univ_succ]
  ring
private theorem coframe_polynomial_electric(z:SourceCoordinateSlice):
    (∑i:Fin 6,∑j:Fin 6,(volume z*squareGradient i z-2*gaugeSquare z*volumeGradient z i)*
      (GaussCoframeKinetic.polynomial z.1 i j*(volume z*squareGradient j z-2*gaugeSquare z*volumeGradient z j)))=
      8*(volume z)^2*wedgePolynomial z := by
  simp only [square_gradient_poly,square_poly,wedge_poly,volume,volumeGradient]
  exact scalar_contact_polynomial z.1 (gaugeGram z)
private def electricContactWeight(z:SourceCoordinateSlice):ℝ:=
  2*∑i:Fin 6,∑j:Fin 6,fderiv ℝ electricWeight z (GaussCoframeCore.coframeDirection i)*
    (GaussCoframeKinetic.coefficient i j z*fderiv ℝ electricWeight z (GaussCoframeCore.coframeDirection j))
private theorem electric_contact_formula(z:physicalChart):electricContactWeight z.val=
    4*n^3/(sourceSigma^2*(volume z.val)^5)*wedgePolynomial z.val := by
  unfold electricContactWeight
  simp only [electric_coframe_derivative,electricCoframeGradient,GaussCoframeKinetic.coefficient]
  have hs:(∑i:Fin 6,∑j:Fin 6,
      (n/(sourceSigma*volume z.val^3)*(volume z.val*squareGradient i z.val-2*gaugeSquare z.val*volumeGradient z.val i))*
      (n/(4*volume z.val)*GaussCoframeKinetic.polynomial z.val.1 i j*
        (n/(sourceSigma*volume z.val^3)*(volume z.val*squareGradient j z.val-2*gaugeSquare z.val*volumeGradient z.val j))))=
      n^3/(4*sourceSigma^2*volume z.val^7)*
        ∑i:Fin 6,∑j:Fin 6,(volume z.val*squareGradient i z.val-2*gaugeSquare z.val*volumeGradient z.val i)*
          (GaussCoframeKinetic.polynomial z.val.1 i j*(volume z.val*squareGradient j z.val-2*gaugeSquare z.val*volumeGradient z.val j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _
    ring
  change 2*_= _
  rw [hs,coframe_polynomial_electric]
  field_simp [(volume_pos z).ne',source_sigma_nonzero]
  ring


private theorem bracket_self(a:NativeLie):nativeBracket a a=0:=by
  have h:=coordinateBracket_skew a a
  change nativeBracket a a= -nativeBracket a a at h
  have hz:(2:ℝ) • nativeBracket a a=0:=by linear_combination (norm:=module) h
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
private theorem bracket_skew(a b:NativeLie):nativeBracket a b= -nativeBracket b a:=coordinateBracket_skew a b
private def cofactorRow(q:Coframe):Matrix (Fin 3) (Fin 3) ℝ:=
  !![q 2*q 5,-q 1*q 5,q 1*q 4-q 2*q 3;0,q 0*q 5,-q 0*q 4;0,0,q 0*q 2]
private theorem magnetic_native(A:Fin 3→NativeLie)(i:Fin 3):
    magneticOfConnection A i=![nativeBracket (A 1) (A 2),nativeBracket (A 2) (A 0),nativeBracket (A 0) (A 1)] i:=rfl
private theorem magnetic_row(z:SourceCoordinateSlice)(i:Fin 3):
    magneticOfConnection (gaugeRow z) i=∑j:Fin 3,cofactorRow z.1 i j • magneticField z j:=by
  have h02:=bracket_skew (connectionField z 0) (connectionField z 2)
  have h10:=bracket_skew (connectionField z 1) (connectionField z 0)
  fin_cases i <;>
    change nativeBracket _ _= _ <;>
    simp only[gaugeRow,cofactorRow,magneticField,magnetic_native,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,bracket_self,
      smul_zero,zero_add,add_zero,h02,h10] <;> norm_num <;> simp only [Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] <;> module
private theorem inverse_cofactor(z:physicalChart)(i j:Fin 3):
    volume z.val*triadInverse z.val.1 j i=cofactorRow z.val.1 i j:=by
  have h0: z.val.1 0≠0:=z.property.1.ne'
  have h2: z.val.1 2≠0:=z.property.2.1.ne'
  have h5: z.val.1 5≠0:=z.property.2.2.1.ne'
  fin_cases i <;> fin_cases j <;>
    simp [volume,triadInverse,cofactorRow] <;> field_simp [h0,h2,h5]
private theorem row_pullback(z:physicalChart)(i:Fin 3):
    magneticOfConnection (gaugeRow z.val) i=
      volume z.val • (∑j:Fin 3,triadInverse z.val.1 j i • magneticField z.val j):=by
  rw [magnetic_row,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul,inverse_cofactor]
private theorem inverse_metric_square(z:SourceCoordinateSlice)(B:Fin 3→NativeLie):
    (∑i:Fin 3,∑j:Fin 3,inverseSpatial z i j*inner ℝ (B i) (B j))=
      ∑k:Fin 3,‖∑i:Fin 3,triadInverse z.1 i k • B i‖^2:=by
  simp only[←real_inner_self_eq_norm_sq,inner_sum,sum_inner,real_inner_smul_left,real_inner_smul_right,
    inverseSpatial,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  simp only[Fin.sum_univ_three]
  ring
private theorem magnetic_metric_return(z:physicalChart):
    (∑i:Fin 3,‖magneticOfConnection (gaugeRow z.val) i‖^2)=
      (volume z.val)^2*(∑i:Fin 3,∑j:Fin 3,inverseSpatial z.val i j*
        inner ℝ (magneticField z.val i) (magneticField z.val j)):=by
  simp_rw [row_pullback,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  rw [←Finset.mul_sum,←inverse_metric_square]

/-- The original triad pulls all three magnetic brackets into precisely the original inverse-spatial form. -/
theorem actual_magnetic_wedge_coefficient(z:physicalChart):
    4*reciprocalVolume z.val*magneticPotential z.val ≤
      (sourceSigma*nativeLiePrice/(4*n^4))*(volume z.val)^3*electricContactWeight z.val:=by
  have h:=actual_native_magnetic_wedge_source (gaugeRow z.val)
  change (∑i:Fin 3,‖magneticOfConnection (gaugeRow z.val) i‖^2) ≤
    (nativeLiePrice/2)*wedgePolynomial z.val at h
  rw [magnetic_metric_return] at h
  have hn:=n_pos
  have hs:=sigma_pos
  have hv:=volume_pos z
  rw [electric_contact_formula]
  unfold reciprocalVolume magneticPotential
  have hden:0<sourceSigma*n*(volume z.val)^2:=by positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  field_simp [hn.ne',hs.ne',hv.ne']
  nlinarith only[h]


/-- The fixed price is generated by the original native Lie map and original source couplings. -/
def magneticPrimitiveFactor:ℝ:=sourceSigma*nativeLiePrice/(4*n^4)
private theorem factor_nonnegative:0 ≤ magneticPrimitiveFactor:=by
  have hn:=n_pos
  have hs:=sigma_pos
  have hB:0 ≤ nativeLiePrice:=by unfold nativeLiePrice;exact sq_nonneg _
  unfold magneticPrimitiveFactor
  positivity
private theorem density_nonnegative(w:QuantumTest)(z:physicalChart):0 ≤ (densityPair w w z.val).re:=by
  have h:=GaussBoundedMultiplier.weighted_square (fun N=>GaussDensityCore.density N z.val)
    (fun N=>(GaussDensityCore.density_pos N z).le) (w z.val)
  exact (sq_nonneg _).trans_eq h.symm
private theorem magnetic_density(w:QuantumTest)(z:SourceCoordinateSlice):
    densityPair w (U (magneticAction w)) z=
      ((reciprocalVolume z*magneticPotential z:ℝ):ℂ)*densityPair w w z:=by
  rw [densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star (w z word)*((reciprocalVolume z:ℂ)*((magneticPotential z:ℂ)*w z word))=_
  push_cast
  ring
private theorem wedge_density(w:QuantumTest)(z:SourceCoordinateSlice):
    densityPair w ((W*wedgeAction) w) z=
      ((volume z^3*electricContactWeight z:ℝ):ℂ)*densityPair w w z:=by
  rw [densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star (w z word)*(((volume z^3:ℝ):ℂ)*((electricContactWeight z:ℂ)*w z word))=_
  push_cast
  ring

/-- The actual magnetic form is paid by the exact V-cubed electric wedge on the same original core. -/
theorem actual_magnetic_electric_contact_payment(w:QuantumTest):
    4*(sourcePair w (U (magneticAction w))).re ≤
      magneticPrimitiveFactor*(sourcePair w ((W*wedgeAction) w)).re:=by
  have hp(z:SourceCoordinateSlice):4*(densityPair w (U (magneticAction w)) z).re ≤
      magneticPrimitiveFactor*(densityPair w ((W*wedgeAction) w) z).re:=by
    rw [magnetic_density,wedge_density]
    simp only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    by_cases hz:z∈physicalChart
    · have h:=mul_le_mul_of_nonneg_right (actual_magnetic_wedge_coefficient ⟨z,hz⟩) (density_nonnegative w ⟨z,hz⟩)
      change 4*reciprocalVolume z*magneticPotential z*(densityPair w w z).re ≤
        magneticPrimitiveFactor*volume z^3*electricContactWeight z*(densityPair w w z).re at h
      nlinarith only[h]
    · have hw:w z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (w.tsupport_subset h))
      simp only[densityPair,hw,map_zero,inner_zero_left,Complex.zero_re,mul_zero,le_refl]
  have hM:MeasureTheory.Integrable (fun z=>(densityPair w (U (magneticAction w)) z).re) GaussHistoryHilbert.configurationMeasure:=
    (densityPair_integrable _ _).re
  have hW:MeasureTheory.Integrable (fun z=>(densityPair w ((W*wedgeAction) w) z).re) GaussHistoryHilbert.configurationMeasure:=
    (densityPair_integrable _ _).re
  have h:=MeasureTheory.integral_mono (hM.const_mul 4) (hW.const_mul magneticPrimitiveFactor) hp
  rw [MeasureTheory.integral_const_mul,MeasureTheory.integral_const_mul] at h
  have hi(f g:QuantumTest):(∫z:SourceCoordinateSlice,(densityPair f g z).re ∂GaussHistoryHilbert.configurationMeasure)=(sourcePair f g).re:=by
    change (∫z:SourceCoordinateSlice,RCLike.re (densityPair f g z) ∂GaussHistoryHilbert.configurationMeasure)=(sourcePair f g).re
    rw [integral_re (densityPair_integrable _ _),←sourcePair_integral]
    rfl
  rw [hi,hi] at h
  exact h

/-- Exact work of two restrictions of one weighted electric source; no endpoint upper bound is an input. -/
def magneticPrimitiveWork(h:ℝ)(w:QuantumTest):ℝ:=
  (2*magneticPrimitiveFactor/h)*
    ((sourcePair (weightedElectricEndpoint h false w) (P (weightedElectricEndpoint h false w))).re-
      (sourcePair (weightedElectricEndpoint h true w) (P (weightedElectricEndpoint h true w))).re)-
    20*magneticPrimitiveFactor*(sourcePair w ((W*U*electricAction) w)).re

/-- The full negative matched square survives the actual primitive's magnetic payment. -/
theorem actual_weighted_magnetic_joint_payment(F:Index)(g:diagonal.domain)(h:ℝ)(hh:0<h)(w:QuantumTest):
    4*(sourcePair w (U (magneticAction w))).re-(n/48)*‖embed (matchedTester w)‖^2 ≤
      magneticPrimitiveWork h w-(n/48)*‖embed (matchedTester w)‖^2:=by
  have hc:=actual_magnetic_electric_contact_payment w
  have hp:=(actual_weighted_electric_midpoint F g h w).2
  have he:magneticPrimitiveWork h w=magneticPrimitiveFactor*(sourcePair w ((W*wedgeAction) w)).re:=by
    unfold magneticPrimitiveWork
    have ht:=congrArg (fun x:ℝ=>(2*magneticPrimitiveFactor/h)*x) hp
    field_simp [hh.ne'] at ht ⊢
    nlinarith only[ht]
  rw [he]
  linarith only[hc]

open FirstCurrentPayerNext ClockPhiHeatCorrectedCovarianceSource SourceClockPhiNormalizedScalarBudget
/-- This is the full forcing update for the same actual corrected state and both electric endpoint restrictions. -/
def weightedElectricForcing(s:ℝ)(hs:0<s)(ξ η h:ℝ)(forward:Bool)
    (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  let w:=correctedCompleteCore s hs ξ η (normalizedState m ell F z hz g)
  let f:=updatedForcing s hs (ξ,η) m ell F z hz g
  f+(if forward then -(h:ℂ) else (h:ℂ)) •
    (weightedElectricCurrent f+bracket diagonalAction weightedElectricCurrent w)

theorem actual_weighted_corrected_full_source(s:ℝ)(hs:0<s)(ξ η h:ℝ)
    (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(forward:Bool):
    let w:=correctedCompleteCore s hs ξ η (normalizedState m ell F z hz g)
    diagonalAction (weightedElectricEndpoint h forward w)=
      weightedElectricForcing s hs ξ η h forward m ell F z hz g+z • weightedElectricEndpoint h forward w:=by
  dsimp only
  have he:=actual_corrected_full_forcing s hs (ξ,η) m ell F z hz g
  dsimp only at he
  unfold weightedElectricEndpoint weightedElectricForcing bracket
  simp only[LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,Module.End.mul_apply,
    LinearMap.sub_apply,map_add,map_smul,he,smul_add,smul_smul]
  module

open FirstCurrentJointBudget FirstCurrentJointBudgetNext SourceLocalizedInverseFormPayment SourceResolventBandLimit
open Filter MeasureTheory
attribute [local irreducible] sourcePair embed normalizedState correctedCompleteCore updatedFirstCurrentRemainder
  correctedScalarNoetherPrice remainingGeometricPrice
private theorem frequency_nonreal(half advanced:Bool)(x:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) x).im≠0:=by
  have hn:=n_pos
  have hp:0<sourceNoetherFrequency half:=by linarith[actual_source_noether_gap half]
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'

/-- The same geometric word retains every derivative/forcing debit and uses its generated electric work for magnetism. -/
def electricGeometricPrice(h:ℝ)(w:QuantumTest)(z:ℂ):ℝ:=
  remainingGeometricPrice w z-4*(sourcePair w (U (magneticAction w))).re+magneticPrimitiveWork h w
private theorem geometric_price_le(F:Index)(g:diagonal.domain)(h:ℝ)(hh:0<h)(w:QuantumTest)(z:ℂ):
    remainingGeometricPrice w z ≤ electricGeometricPrice h w z:=by
  have hm:=actual_weighted_magnetic_joint_payment F g h hh w
  unfold electricGeometricPrice
  linarith only[hm]

def electricGeometricGap(s:ℝ)(hs:0<s)(ξ η h:ℝ)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(x:ℝ)(g:diagonal.domain):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let w:=correctedCompleteCore s hs ξ η (normalizedState m ell F z hz g)
  updatedFirstCurrentRemainder s hs (ξ,η) m ell F z hz g-
    (scalarNoetherFactor half*correctedScalarNoetherPrice s hs ξ η half advanced m ell F x g+
      electricGeometricPrice h w z)

/-- One common source event pays the actual R difference for every finite weighted-electric update,
while its complete scalar Noether and remaining electric/geometric source words stay signed. -/
theorem actual_electric_geometric_common_payment(half:Bool)(g:diagonal.domain):
    ∀ ε:ℝ,0<ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,∀ s:ℝ,∀ hs:0<s,
      s ≤ jointClockWindow half → ∀ ξ η h:ℝ,0<h →
      (∫⁻x:ℝ,ENNReal.ofReal (electricGeometricGap s hs ξ η h half advanced m ell F x g)) ≤ ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_remaining_geometric_common_payment half g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced s hs ht ξ η h hh
  refine (lintegral_mono (fun x=>?_)).trans (hF advanced s hs ht ξ η)
  apply ENNReal.ofReal_le_ofReal
  dsimp only[electricGeometricGap,remainingGeometricGap]
  exact sub_le_sub_left (add_le_add le_rfl (geometric_price_le F g h hh _ _)) _
end LowEnergy.FirstCurrentGeometricPayer
