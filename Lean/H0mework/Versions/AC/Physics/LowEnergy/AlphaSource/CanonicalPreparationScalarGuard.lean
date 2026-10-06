import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationGaugeGuard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationChartGuard
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineP286GaugeConnectionVariationDensity
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualFlow
open PreparationCoordinates PreparationScalarCoordinates CanonicalPreparationCutoff
open GaussHistoryHilbert
open Set
open scoped RealInnerProductSpace ContDiff

private theorem scalar_source_center (i : Fin 61) :
    flatSource ⟨6+i.val,by omega⟩=0 := by
  unfold flatSource
  split_ifs with hc hg hn
  · rcases hc with h|h|h
    · have val : 6+i.val=0 := congrArg Fin.val h
      omega
    · have val : 6+i.val=2 := congrArg Fin.val h
      omega
    · have val : 6+i.val=5 := congrArg Fin.val h
      omega
  · rcases hg with h|h|h
    · have val : 6+i.val=67 := congrArg Fin.val h
      omega
    · have val : 6+i.val=77 := congrArg Fin.val h
      omega
    · have val : 6+i.val=94 := congrArg Fin.val h
      omega
  · have val : 6+i.val=95 := congrArg Fin.val hn
    omega
  · rfl

theorem scalar_box_coordinates (z : FlatConfiguration) (box : z ∈ sourceClosedBox) (i : Fin 61) :
    |scalarFree (fullCoordinates.symm z).2.1 i|≤2*sourceRadius := by
  have bound:=box ⟨6+i.val,by omega⟩
  rw [scalar_source_center,sub_zero] at bound
  have coordinate : scalarFree (fullCoordinates.symm z).2.1 i=z ⟨6+i.val,by omega⟩ := by
    change scalarFree (scalarFree.symm (splitCoordinates z).2.1) i=_
    exact congrFun (scalarFree.apply_symm_apply _) i
  rw [coordinate]
  exact bound

theorem scalar_box_norm (z : FlatConfiguration) (box : z ∈ sourceClosedBox) :
    ‖((fullCoordinates.symm z).2.1 : Scalar)‖≤16*sourceRadius := by
  let x:=scalarFree (fullCoordinates.symm z).2.1
  have squared : ‖((fullCoordinates.symm z).2.1 : Scalar)‖^2=
      ∑ i : Fin 61, scalarGramWeight i*x i*x i := by
    simpa only [x,LinearEquiv.symm_apply_apply] using scalar_norm_sq x
  have weight (i : Fin 61) : 0 ≤ scalarGramWeight i ∧ scalarGramWeight i ≤ 1 := by
    unfold scalarGramWeight
    split_ifs <;> norm_num
  have term (i : Fin 61) : scalarGramWeight i*x i*x i≤(2*sourceRadius)^2 := by
    have raw:=scalar_box_coordinates z box i
    have square:=pow_le_pow_left₀ (abs_nonneg (x i)) raw 2
    simp only [sq_abs] at square
    calc
      scalarGramWeight i*x i*x i = scalarGramWeight i*(x i)^2 := by ring
      _ ≤ (x i)^2 := by nlinarith [weight i,sq_nonneg (x i)]
      _ ≤ (2*sourceRadius)^2 := square
  have sum:=Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin 61) _ => term i)
  rw [← squared] at sum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at sum
  nlinarith [norm_nonneg (((fullCoordinates.symm z).2.1 : Scalar)),radius_small.1]

abbrev NormalCoordinates := EuclideanSpace ℝ (Fin 9)

def normalRead (a : NativeLie) : NormalCoordinates :=
  let c:=nativeCoordinates a
  WithLp.toLp 2 ![c.1 2,c.1 3,c.1 4,c.1 5,c.1 7,c.2.1 0,c.2.1 1,c.2.1 2,c.2.2]

def normalBuild (x : NormalCoordinates) : NativeLie :=
  nativeCoordinates.symm (![0,0,x 0,x 1,x 2,x 3,0,x 4],![x 5,x 6,x 7],x 8)

def stabilizerPart (a : NativeLie) : stabilizer :=
  let c:=nativeCoordinates a
  colorStabilizer (![2*c.1 1,2*c.1 0,2*c.1 6])

theorem native_decomposition (a : NativeLie) :
    a=normalBuild (normalRead a)+(stabilizerPart a : NativeLie) := by
  apply nativeCoordinates.injective
  rw [map_add]
  change nativeCoordinates a=nativeCoordinates (normalBuild (normalRead a))+
    nativeCoordinates (colorCombination (![2*(nativeCoordinates a).1 1,
      2*(nativeCoordinates a).1 0,2*(nativeCoordinates a).1 6]))
  rw [colorCombination_coordinates]
  simp only [normalBuild,LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [normalRead]
  · apply Prod.ext
    · ext i; fin_cases i <;> simp [normalRead]
    · simp [normalRead]

theorem stabilizer_affine_action (a : stabilizer) (x : scalarSlice) :
    action (vacuum+(x : Scalar)) a.val ∈ scalarSlice := by
  change scalarP286ActionBilinear a.val (vacuum+(x : Scalar)) ∈ scalarSlice
  rw [map_add]
  have zero : scalarP286ActionBilinear a.val vacuum=0 := a.property
  rw [zero,zero_add]
  exact (scalarAction a x).property

theorem kernel_native_pairing (phi : Scalar) (a : broken) (zero : consistency phi a=0)
    (b : NativeLie) : inner ℝ (orbit b) (action phi a.val)=0 := by
  let pb:=broken.orthogonalProjectionOnto b
  have difference : b-pb.val ∈ stabilizer := by
    have h:=broken.sub_starProjection_mem_orthogonal b
    simpa only [pb,Submodule.coe_orthogonalProjectionOnto_apply,broken,Submodule.orthogonal_orthogonal] using h
  have orbit_same : orbit b=orbit pb.val := by
    have vanishes : orbit (b-pb.val)=0 := difference
    rw [map_sub,sub_eq_zero] at vanishes
    exact vanishes
  rw [orbit_same]
  have pair:=consistency_pairing phi pb a
  rw [zero,inner_zero_right] at pair
  exact pair.symm

theorem kernel_normal_pairing (x : scalarSlice) (a : broken)
    (zero : consistency (vacuum+(x : Scalar)) a=0) :
    inner ℝ (orbit (normalBuild (normalRead a.val)))
      (action (vacuum+(x : Scalar)) (normalBuild (normalRead a.val)))=0 := by
  have original:=kernel_native_pairing (vacuum+(x : Scalar)) a zero
    (normalBuild (normalRead a.val))
  have sum : action (vacuum+(x : Scalar)) a.val=
      action (vacuum+(x : Scalar)) (normalBuild (normalRead a.val))+
        action (vacuum+(x : Scalar)) (stabilizerPart a.val).val := by
    nth_rw 1 [native_decomposition a.val]
    exact map_add _ _ _
  rw [sum,inner_add_right] at original
  have tangent:=stabilizer_affine_action (stabilizerPart a.val) x
  have orth:= (Submodule.mem_orthogonal _ _).mp tangent
    (orbit (normalBuild (normalRead a.val))) ⟨_,rfl⟩
  rw [orth,add_zero] at original
  exact original

theorem broken_zero_of_normal_zero (a : broken) (zero : normalRead a.val=0) : a=0 := by
  have ha:=native_decomposition a.val
  rw [zero] at ha
  have buildzero : normalBuild 0=0 := by
    apply nativeCoordinates.injective
    simp [normalBuild]
  rw [buildzero,zero_add] at ha
  have stab : a.val ∈ stabilizer := ha ▸ (stabilizerPart a.val).property
  have both : a.val ∈ stabilizer ⊓ stabilizerᗮ := ⟨stab,a.property⟩
  have value : a.val=0 := by simpa only [Submodule.inf_orthogonal_eq_bot,Submodule.mem_bot] using both
  exact Subtype.ext value

theorem normal_norm_squared (x : NormalCoordinates) :
    ‖x‖^2=(x 0)^2+(x 1)^2+(x 2)^2+(x 3)^2+(x 4)^2+
      (x 5)^2+(x 6)^2+(x 7)^2+(x 8)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ]
  ring

theorem normal_orbit_squared (x : NormalCoordinates) :
    ‖orbit (normalBuild x)‖^2=
      2*((x 0)^2+(x 1)^2+(x 2)^2+(x 3)^2+(x 5)^2+(x 6)^2)+
        (x 4)^2+(x 7)^2+(x 8)^2+(x 4-x 7+x 8)^2 := by
  rw [← real_inner_self_eq_norm_sq,scalar_inner_lex]
  simp_rw [normalBuild,sourceOrbit_all]
  simp [Fin.sum_univ_succ,sourceOrbit35]
  ring

theorem normal_orbit_lower (x : NormalCoordinates) : ‖x‖^2≤‖orbit (normalBuild x)‖^2 := by
  rw [normal_norm_squared,normal_orbit_squared]
  nlinarith [sq_nonneg (x 0),sq_nonneg (x 1),sq_nonneg (x 2),sq_nonneg (x 3),
    sq_nonneg (x 5),sq_nonneg (x 6),sq_nonneg (x 4-x 7+x 8)]

theorem normal_orbit_upper (x : NormalCoordinates) : ‖orbit (normalBuild x)‖≤2*‖x‖ := by
  have triple : (x 4-x 7+x 8)^2≤3*((x 4)^2+(x 7)^2+(x 8)^2) := by
    nlinarith [sq_nonneg (x 4+x 7),sq_nonneg (x 4-x 8),sq_nonneg (x 7+x 8)]
  have bounded : ‖orbit (normalBuild x)‖^2≤4*‖x‖^2 := by
    rw [normal_norm_squared,normal_orbit_squared]
    nlinarith [sq_nonneg (x 0),sq_nonneg (x 1),sq_nonneg (x 2),sq_nonneg (x 3),
      sq_nonneg (x 5),sq_nonneg (x 6)]
  nlinarith [norm_nonneg (orbit (normalBuild x)),norm_nonneg x]

private theorem three_product_bound (M : Matrix (Fin 3) (Fin 3) ℂ)
    (bound : ∀ i j, ‖M i j‖≤1) (a b c d e f : Fin 3) :
    ‖M a b*M c d*M e f‖≤1 := by
  rw [norm_mul,norm_mul]
  calc
    ‖M a b‖*‖M c d‖*‖M e f‖≤1*1*1 := by
      gcongr
      · exact bound a b
      · exact bound c d
      · exact bound e f
    _ = 1 := by norm_num

private theorem norm_three_sum (a b c : ℂ) :
    ‖a+b+c‖≤‖a‖+‖b‖+‖c‖ := by
  exact (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)

private theorem determinant_three_bound (M : Matrix (Fin 3) (Fin 3) ℂ)
    (bound : ∀ i j, ‖M i j‖≤1) : ‖M.det‖≤6 := by
  have formula : M.det=
      (M 0 0*M 1 1*M 2 2+M 0 1*M 1 2*M 2 0+M 0 2*M 1 0*M 2 1)-
      (M 0 0*M 1 2*M 2 1+M 0 1*M 1 0*M 2 2+M 0 2*M 1 1*M 2 0) := by
    rw [Matrix.det_fin_three]
    ring
  rw [formula]
  have plus : ‖M 0 0*M 1 1*M 2 2+M 0 1*M 1 2*M 2 0+M 0 2*M 1 0*M 2 1‖≤3 := by
    have triangle:=norm_three_sum (M 0 0*M 1 1*M 2 2) (M 0 1*M 1 2*M 2 0) (M 0 2*M 1 0*M 2 1)
    linarith [three_product_bound M bound 0 0 1 1 2 2,
      three_product_bound M bound 0 1 1 2 2 0,three_product_bound M bound 0 2 1 0 2 1]
  have minus : ‖M 0 0*M 1 2*M 2 1+M 0 1*M 1 0*M 2 2+M 0 2*M 1 1*M 2 0‖≤3 := by
    have triangle:=norm_three_sum (M 0 0*M 1 2*M 2 1) (M 0 1*M 1 0*M 2 2) (M 0 2*M 1 1*M 2 0)
    linarith [three_product_bound M bound 0 0 1 2 2 1,
      three_product_bound M bound 0 1 1 0 2 2,three_product_bound M bound 0 2 1 1 2 0]
  have triangle:=norm_sub_le (M 0 0*M 1 1*M 2 2+M 0 1*M 1 2*M 2 0+M 0 2*M 1 0*M 2 1)
    (M 0 0*M 1 2*M 2 1+M 0 1*M 1 0*M 2 2+M 0 2*M 1 1*M 2 0)
  linarith

open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorYukawaMassSpectrum StageNineCoframeScalarMatterRegularity StageNineExteriorMotherLieRepresentation
open SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal

local instance motherOrder : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective
local instance : Preorder SU7MotherIndex := motherOrder.toPreorder
local instance : LT SU7MotherIndex := motherOrder.toLT
local instance : LE SU7MotherIndex := motherOrder.toLE
private theorem position_value (output : ScalarBasisIndex) (col : Fin 4) :
    Set.powersetCard.ofFinEmbEquiv.symm output col = (exteriorPositionEquiv output col).val := rfl

private def slotMatrix (M : Matrix SU7MotherIndex SU7MotherIndex ℂ) (output input : ScalarBasisIndex)
    (slot : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := fun row col =>
  if row = slot then M (exteriorPositionEquiv output col).val (exteriorPositionEquiv input row).val
  else if (exteriorPositionEquiv input row).val = (exteriorPositionEquiv output col).val then 1 else 0

private theorem exterior_coordinate (M : SU7MotherLieMatrix) (output input : ScalarBasisIndex) :
    (su7ExteriorBasis 4).repr (exteriorBasisLieAction 4 M input) output =
      ∑ slot : Fin 4, (slotMatrix (M : Matrix SU7MotherIndex SU7MotherIndex ℂ) output input slot).det := by
  unfold exteriorBasisLieAction
  rw [map_sum]
  change (∑ slot : Fin 4, (su7ExteriorBasis 4).repr
    ((exteriorPower.ιMulti ℂ 4) (exteriorBasisLieActionInput 4 M input slot)) output) = _
  apply Finset.sum_congr rfl
  intro slot _
  rw [su7ExteriorBasis, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  apply congrArg Matrix.det
  ext row col
  by_cases h : row = slot
  · subst row
    simp [slotMatrix, exteriorBasisLieActionInput, fundamentalMotherLieAction,
      su7FundamentalBasis, Matrix.mulVecLin, position_value]
  · simp [slotMatrix, exteriorBasisLieActionInput, h, Ne.symm h, position_value, Finsupp.single_apply, eq_comm]


private theorem slot_cofactor (M : Matrix SU7MotherIndex SU7MotherIndex ℂ)
    (output input : ScalarBasisIndex) (slot : Fin 4) :
    (slotMatrix M output input slot).det=∑ j : Fin 4,
      (-1 : ℂ)^((slot : ℕ)+(j : ℕ))*M (exteriorPositionEquiv output j).val
        (exteriorPositionEquiv input slot).val*
        Matrix.det (fun r c : Fin 3 =>
          if (exteriorPositionEquiv input (slot.succAbove r)).val=
            (exteriorPositionEquiv output (j.succAbove c)).val then (1 : ℂ) else 0) := by
  rw [Matrix.det_succ_row _ slot]
  apply Finset.sum_congr rfl
  intro j _
  have minor : (slotMatrix M output input slot).submatrix slot.succAbove j.succAbove=
      fun r c : Fin 3 =>
        if (exteriorPositionEquiv input (slot.succAbove r)).val=
          (exteriorPositionEquiv output (j.succAbove c)).val then (1 : ℂ) else 0 := by
    ext r c
    simp [Matrix.submatrix_apply,slotMatrix,Fin.succAbove_ne]
  rw [minor]
  simp [slotMatrix]

private theorem slot_bound (M : Matrix SU7MotherIndex SU7MotherIndex ℂ)
    (bound : ∀ i j, ‖M i j‖≤1) (output input : ScalarBasisIndex) (slot : Fin 4) :
    ‖(slotMatrix M output input slot).det‖≤24 := by
  rw [slot_cofactor]
  have each (j : Fin 4) :
      ‖(-1 : ℂ)^((slot : ℕ)+(j : ℕ))*M (exteriorPositionEquiv output j).val
        (exteriorPositionEquiv input slot).val*
        Matrix.det (fun r c : Fin 3 =>
          if (exteriorPositionEquiv input (slot.succAbove r)).val=
            (exteriorPositionEquiv output (j.succAbove c)).val then (1 : ℂ) else 0)‖≤6 := by
    rw [norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    have minor := determinant_three_bound
      (fun r c : Fin 3 =>
        if (exteriorPositionEquiv input (slot.succAbove r)).val=
          (exteriorPositionEquiv output (j.succAbove c)).val then (1 : ℂ) else 0)
      (by intro r c; split_ifs <;> norm_num)
    exact (mul_le_mul_of_nonneg_right (bound _ _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using minor)
  have triangle:=norm_sum_le Finset.univ (fun j : Fin 4 =>
    (-1 : ℂ)^((slot : ℕ)+(j : ℕ))*M (exteriorPositionEquiv output j).val
      (exteriorPositionEquiv input slot).val*
      Matrix.det (fun r c : Fin 3 =>
        if (exteriorPositionEquiv input (slot.succAbove r)).val=
          (exteriorPositionEquiv output (j.succAbove c)).val then (1 : ℂ) else 0))
  have total:=Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin 4) _ => each j)
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  linarith

theorem exterior_coordinate_bound (M : SU7MotherLieMatrix)
    (bound : ∀ i j, ‖M.val i j‖≤1) (output input : ScalarBasisIndex) :
    ‖(su7ExteriorBasis 4).repr (exteriorBasisLieAction 4 M input) output‖≤96 := by
  rw [exterior_coordinate]
  have triangle:=norm_sum_le Finset.univ (fun slot : Fin 4 => (slotMatrix M.val output input slot).det)
  have total:=Finset.sum_le_sum (s := Finset.univ)
    (fun (slot : Fin 4) _ => slot_bound M.val bound output input slot)
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  linarith

def scalarOperator (M : SU7MotherLieMatrix) : Scalar →ₗ[ℂ] Scalar :=
  scalarCoordinateEquiv.toLinearMap.comp
    ((exteriorMotherLieAction 4 M).comp scalarCoordinateEquiv.symm.toLinearMap)

theorem scalar_operator_coordinates (M : SU7MotherLieMatrix) (sigma : Scalar) (output : ScalarBasisIndex) :
    scalarOperator M sigma output=∑ input : ScalarBasisIndex,
      sigma input*((su7ExteriorBasis 4).repr (exteriorBasisLieAction 4 M input) output) := by
  have coordinate (i : ScalarBasisIndex) :
      (su7ExteriorBasis 4).repr (scalarCoordinateEquiv.symm sigma) i=sigma i :=
    congrArg (fun s : Scalar => s i) (scalarCoordinateEquiv.apply_symm_apply sigma)
  have build:=(su7ExteriorBasis 4).sum_repr (scalarCoordinateEquiv.symm sigma)
  simp_rw [coordinate] at build
  change scalarCoordinateEquiv ((exteriorMotherLieAction 4 M) (scalarCoordinateEquiv.symm sigma)) output=_
  rw [← build,map_sum,map_sum]
  simp_rw [map_smul,exteriorMotherLieAction_basis_slot]
  let read : Scalar →ₗ[ℂ] ℂ := (LinearMap.proj output).comp
    (WithLp.linearEquiv 2 ℂ (ScalarBasisIndex → ℂ)).toLinearMap
  change read (∑ input : ScalarBasisIndex,
    sigma input • scalarCoordinateEquiv (exteriorBasisLieAction 4 M input))=_
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

private theorem euclidean_norm_le_sum {K : Type*} [RCLike K] {I : Type*} [Fintype I]
    (x : EuclideanSpace K I) : ‖x‖≤∑ i : I,‖x i‖ := by
  classical
  let unit : I → EuclideanSpace K I := fun i => PiLp.single 2 i (x i)
  have build : x=∑ i : I,unit i := by
    ext i
    simp [unit]
  calc
    ‖x‖=‖∑ i : I,unit i‖ := congrArg norm build
    _ ≤ ∑ i : I,‖unit i‖ := norm_sum_le _ _
    _ = ∑ i : I,‖x i‖ := by simp [unit]

private theorem scalar_index_card : Fintype.card ScalarBasisIndex=35 := by
  rw [← Fintype.card_congr lexEquiv]
  simp

theorem scalar_operator_point_bound (M : SU7MotherLieMatrix)
    (bound : ∀ i j, ‖M.val i j‖≤1) (sigma : Scalar) (output : ScalarBasisIndex) :
    ‖scalarOperator M sigma output‖≤3360*‖sigma‖ := by
  rw [scalar_operator_coordinates]
  have each (input : ScalarBasisIndex) :
      ‖sigma input*((su7ExteriorBasis 4).repr (exteriorBasisLieAction 4 M input) output)‖≤96*‖sigma‖ := by
    rw [norm_mul]
    have coord:=PiLp.norm_apply_le sigma input
    have action:=exterior_coordinate_bound M bound output input
    calc
      _ ≤ ‖sigma‖*96 := mul_le_mul coord action (norm_nonneg _) (norm_nonneg _)
      _ = 96*‖sigma‖ := mul_comm _ _
  have triangle:=norm_sum_le Finset.univ (fun input : ScalarBasisIndex =>
    sigma input*((su7ExteriorBasis 4).repr (exteriorBasisLieAction 4 M input) output))
  have total:=Finset.sum_le_sum (s := Finset.univ) (fun (input : ScalarBasisIndex) _ => each input)
  norm_num only [Finset.sum_const,Finset.card_univ,scalar_index_card,nsmul_eq_mul] at total
  nlinarith

theorem scalar_operator_bound (M : SU7MotherLieMatrix)
    (bound : ∀ i j, ‖M.val i j‖≤1) (sigma : Scalar) :
    ‖scalarOperator M sigma‖≤117600*‖sigma‖ := by
  have total:=Finset.sum_le_sum (s := Finset.univ)
    (fun (i : ScalarBasisIndex) _ => scalar_operator_point_bound M bound sigma i)
  norm_num only [Finset.sum_const,Finset.card_univ,scalar_index_card,nsmul_eq_mul] at total
  have triangle:=euclidean_norm_le_sum (scalarOperator M sigma)
  nlinarith

private def normalColor (x : NormalCoordinates) : SU3BlockLieMatrix :=
  ⟨!![(0 : ℂ),0,x 0+x 1*Complex.I;
      0,x 4*Complex.I,x 2+x 3*Complex.I;
      -x 0+x 1*Complex.I,-x 2+x 3*Complex.I,-x 4*Complex.I], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply] <;> ring
    · simp [Matrix.trace,Fin.sum_univ_three]⟩

private def normalWeak (x : NormalCoordinates) : SU2BlockLieMatrix :=
  ⟨!![x 7*Complex.I,x 5+x 6*Complex.I;
      -x 5+x 6*Complex.I,-x 7*Complex.I], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply] <;> ring
    · simp [Matrix.trace,Fin.sum_univ_succ]⟩

private def normalHyper (x : NormalCoordinates) : HyperchargeLieScalar :=
  ⟨x 8*Complex.I,by
    change star ((x 8 : ℂ)*Complex.I)=-((x 8 : ℂ)*Complex.I)
    simp⟩

private def normalBlock (x : NormalCoordinates) : P286LieBlockData :=
  (normalColor x,normalWeak x,normalHyper x)

theorem normal_block_build (x : NormalCoordinates) :
    p286CoordinateEquiv (normalBlock x)=normalBuild x := by
  apply nativeCoordinates.injective
  rw [nativeCoordinates_apply]
  simp only [normalBuild,LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [normalBlock,normalColor]
  · apply Prod.ext
    · ext i; fin_cases i <;> simp [normalBlock,normalWeak]
    · simp [normalBlock,normalHyper]

private def normalMother (i : Fin 9) : SU7MotherLieMatrix :=
  p286LieBlockEmbed (normalBlock (PiLp.single 2 i 1))

private def normalFullMatrix (x : NormalCoordinates) : Matrix (Fin 7) (Fin 7) ℂ :=
  !![(0 : ℂ),0,x 0+x 1*Complex.I,0,0,0,0;
     0,x 4*Complex.I,x 2+x 3*Complex.I,0,0,0,0;
     -x 0+x 1*Complex.I,-x 2+x 3*Complex.I,-x 4*Complex.I,0,0,0,0;
     0,0,0,x 7*Complex.I,x 5+x 6*Complex.I,0,0;
     0,0,0,-x 5+x 6*Complex.I,-x 7*Complex.I,0,0;
     0,0,0,0,0,x 8*Complex.I,0;
     0,0,0,0,0,0,-x 8*Complex.I]

private theorem normal_numeric (x : NormalCoordinates) (a b : Fin 7) :
    (p286LieBlockEmbed (normalBlock x)).val (smBlockIndexEquivFin7.symm a)
      (smBlockIndexEquivFin7.symm b)=normalFullMatrix x a b := by
  fin_cases a <;> fin_cases b <;> try rfl
  change -((x 8 : ℂ)*Complex.I)=-(x 8 : ℂ)*Complex.I
  ring

theorem normal_mother_entry_bound (k : Fin 9) (i j : SU7MotherIndex) :
    ‖(normalMother k).val i j‖≤1 := by
  obtain ⟨a,rfl⟩:=smBlockIndexEquivFin7.symm.surjective i
  obtain ⟨b,rfl⟩:=smBlockIndexEquivFin7.symm.surjective j
  change ‖(p286LieBlockEmbed (normalBlock (PiLp.single 2 k 1))).val
    (smBlockIndexEquivFin7.symm a) (smBlockIndexEquivFin7.symm b)‖≤1
  rw [normal_numeric]
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    norm_num [normalFullMatrix,PiLp.single_apply]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

theorem normal_unit_action (i : Fin 9) (sigma : Scalar) :
    action sigma (normalBuild (PiLp.single 2 i 1))=scalarOperator (normalMother i) sigma := by
  rw [← normal_block_build]
  change scalarMotherLieAction (p286LieBlockEmbed
    (p286CoordinateEquiv.symm (p286CoordinateEquiv (normalBlock (PiLp.single 2 i 1))))) sigma=_
  rw [p286CoordinateEquiv.symm_apply_apply]
  rfl

theorem normal_unit_action_bound (i : Fin 9) (sigma : Scalar) :
    ‖action sigma (normalBuild (PiLp.single 2 i 1))‖≤117600*‖sigma‖ := by
  rw [normal_unit_action]
  exact scalar_operator_bound _ (normal_mother_entry_bound i) sigma

private def normalBuildLinear : NormalCoordinates →ₗ[ℝ] NativeLie where
  toFun := normalBuild
  map_add' x y := by
    apply nativeCoordinates.injective
    simp only [normalBuild,LinearEquiv.apply_symm_apply,map_add]
    apply Prod.ext
    · ext i; fin_cases i <;> simp
    · apply Prod.ext
      · ext i; fin_cases i <;> simp
      · rfl
  map_smul' r x := by
    apply nativeCoordinates.injective
    simp only [normalBuild,LinearEquiv.apply_symm_apply,map_smul]
    apply Prod.ext
    · ext i; fin_cases i <;> simp
    · apply Prod.ext
      · ext i; fin_cases i <;> simp
      · rfl

theorem normal_action_bound (x : NormalCoordinates) (sigma : Scalar) :
    ‖action sigma (normalBuild x)‖≤1058400*‖x‖*‖sigma‖ := by
  let unit : Fin 9 → NormalCoordinates := fun i => PiLp.single 2 i 1
  have build : x=∑ i : Fin 9,x i • unit i := by
    ext i
    simp [unit,Pi.single_apply,mul_ite]
  have decomposition : action sigma (normalBuild x)=
      ∑ i : Fin 9,x i • action sigma (normalBuild (unit i)) := by
    change action sigma (normalBuildLinear x)=_
    nth_rw 1 [build]
    rw [map_sum,map_sum]
    simp only [map_smul]
    rfl
  rw [decomposition]
  have each (i : Fin 9) : ‖x i • action sigma (normalBuild (unit i))‖≤117600*‖x‖*‖sigma‖ := by
    rw [norm_smul]
    have point:=PiLp.norm_apply_le x i
    have action:=normal_unit_action_bound i sigma
    calc
      _ ≤ ‖x‖*(117600*‖sigma‖) := mul_le_mul point action (norm_nonneg _) (norm_nonneg _)
      _ = 117600*‖x‖*‖sigma‖ := by ring
  have triangle:=norm_sum_le Finset.univ (fun i : Fin 9 => x i • action sigma (normalBuild (unit i)))
  have total:=Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin 9) _ => each i)
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  nlinarith

theorem radius_strong : sourceRadius < 1/1000000000000 := by
  norm_num [sourceRadius]

theorem original_scalar_kernel_zero (z : FlatConfiguration) (box : z ∈ sourceClosedBox)
    (a : broken) (zero : consistency (vacuum+((fullCoordinates.symm z).2.1 : Scalar)) a=0) : a=0 := by
  let sigma:=(fullCoordinates.symm z).2.1
  let x:=normalRead a.val
  have zeroPair:=kernel_normal_pairing sigma a zero
  change inner ℝ (orbit (normalBuild x)) (action (vacuum+(sigma : Scalar)) (normalBuild x))=0 at zeroPair
  have split : action (vacuum+(sigma : Scalar)) (normalBuild x)=
      orbit (normalBuild x)+action (sigma : Scalar) (normalBuild x) := by
    change StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
      (normalBuild x) (vacuum+(sigma : Scalar))=_
    exact map_add _ _ _
  rw [split,inner_add_right,real_inner_self_eq_norm_sq] at zeroPair
  have innerBound:=norm_inner_le_norm (𝕜 := ℝ) (orbit (normalBuild x)) (action (sigma : Scalar) (normalBuild x))
  change |inner ℝ (orbit (normalBuild x)) (action (sigma : Scalar) (normalBuild x))|≤
    ‖orbit (normalBuild x)‖*‖action (sigma : Scalar) (normalBuild x)‖ at innerBound
  have actionBound:=normal_action_bound x (sigma : Scalar)
  have sigmaBound:=scalar_box_norm z box
  have orbitBound:=normal_orbit_upper x
  have lower:=normal_orbit_lower x
  have perturb : ‖orbit (normalBuild x)‖*‖action (sigma : Scalar) (normalBuild x)‖≤
      33868800*sourceRadius*‖x‖^2 := by
    calc
      _ ≤ (2*‖x‖)*(1058400*‖x‖*(16*sourceRadius)) := by
        apply mul_le_mul orbitBound ?_ (norm_nonneg _) (by positivity)
        exact actionBound.trans (mul_le_mul_of_nonneg_left sigmaBound (by positivity))
      _ = _ := by ring
  have normZero : ‖x‖=0 := by
    have sign : inner ℝ (orbit (normalBuild x)) (action (sigma : Scalar) (normalBuild x))≤0 := by
      nlinarith [sq_nonneg ‖orbit (normalBuild x)‖]
    rw [abs_of_nonpos sign] at innerBound
    nlinarith [radius_strong,norm_nonneg x,radius_small.1]
  apply broken_zero_of_normal_zero a
  exact norm_eq_zero.mp normZero

theorem original_scalar_injective (z : FlatConfiguration) (box : z ∈ sourceClosedBox) :
    Function.Injective (consistency (vacuum+((fullCoordinates.symm z).2.1 : Scalar))) := by
  intro a b equal
  have zero : consistency (vacuum+((fullCoordinates.symm z).2.1 : Scalar)) (a-b)=0 := by
    rw [map_sub,equal,sub_self]
  exact sub_eq_zero.mp (original_scalar_kernel_zero z box (a-b) zero)

theorem original_scalar_chart (z : FlatConfiguration) (box : z ∈ sourceClosedBox) :
    (fullCoordinates.symm z).2.1 ∈ scalarChart := by
  change (consistency (vacuum+((fullCoordinates.symm z).2.1 : Scalar))).det≠0
  exact (LinearEquiv.ofInjectiveEndo _ (original_scalar_injective z box)).isUnit_det'.ne_zero

theorem actual_source_chart_guard : SourceChartGuard := by
  apply sourceChartGuard_of_residual
  intro z box
  have pos:=original_positive_guards z box
  exact ⟨original_scalar_chart z box,
    jacobian_positive (fullCoordinates.symm z).2.2 pos.2.2.2.1 pos.2.2.2.2⟩

def actualNativeLocalizer : CanonicalGradedSpatial.Localizer := nativeLocalizer actual_source_chart_guard

theorem actualNativeLocalizer_source : actualNativeLocalizer GaussHistoryHilbert.sourcePoint.val=1 :=
  nativeLocalizer_at_source _

end LowEnergy.PreparationChartGuard
