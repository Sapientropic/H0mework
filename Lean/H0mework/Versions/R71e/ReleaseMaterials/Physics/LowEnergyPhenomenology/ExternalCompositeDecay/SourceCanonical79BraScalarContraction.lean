import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraScalarRows0
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraScalarRows1
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraScalarRows2
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraScalarRows3
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators Matrix

def canonicalScalar : ℂ :=
  (11883666571412341/35669395945134500 : ℂ) -
  (3409605742/277762698775 : ℂ) -
  (14903039908/277762698775 : ℂ) +
  (1088882209340648877779/4396698917687141306250 : ℂ)

private theorem scalar_sum_value (dual : Bool) :
    (∑i : Fin 79,scalarRow dual i) = (150913290192423496344222314491299/81415930471860130022585251656250 : ℂ)/(lapse : ℂ) := by
  have hf : scalarRow dual = ![(15650764710741639/356693959451345000 : ℂ)/(lapse : ℂ), (15650764710741639/356693959451345000 : ℂ)/(lapse : ℂ), (-13584123/103992025 : ℂ)/(lapse : ℂ), (-13584123/103992025 : ℂ)/(lapse : ℂ), (-2075067/20798405 : ℂ)/(lapse : ℂ), (-2075067/20798405 : ℂ)/(lapse : ℂ), (-301200223533643473003/5862265223582855075000 : ℂ)/(lapse : ℂ), (-132025298273063428347/5862265223582855075000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (27/500 : ℂ)/(lapse : ℂ), (81/500 : ℂ)/(lapse : ℂ), (2169/775000 : ℂ)/(lapse : ℂ), (9/1240 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (108/2671 : ℂ)/(lapse : ℂ), (108/2671 : ℂ)/(lapse : ℂ), (-15699977499658851/173997053390900000 : ℂ)/(lapse : ℂ), (1412174414989630953/7133879189026900000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-15332625/3301651867 : ℂ)/(lapse : ℂ), (-175882887/6603303734 : ℂ)/(lapse : ℂ), (9/1240 : ℂ)/(lapse : ℂ), (9081/775000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (108/2671 : ℂ)/(lapse : ℂ), (108/2671 : ℂ)/(lapse : ℂ), (-15699977499658851/173997053390900000 : ℂ)/(lapse : ℂ), (1412174414989630953/7133879189026900000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-15332625/3301651867 : ℂ)/(lapse : ℂ), (-175882887/6603303734 : ℂ)/(lapse : ℂ), (1800259882262973/209819976147850000 : ℂ)/(lapse : ℂ), (1800259882262973/209819976147850000 : ℂ)/(lapse : ℂ), (38418123987/1388813493875 : ℂ)/(lapse : ℂ), (38418123987/1388813493875 : ℂ)/(lapse : ℂ), (4435239753/1388813493875 : ℂ)/(lapse : ℂ), (4435239753/1388813493875 : ℂ)/(lapse : ℂ), (-53937990545022/1682142101458495 : ℂ)/(lapse : ℂ), (154935472028241/6728568405833980 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (-42969843/6603303734 : ℂ)/(lapse : ℂ), (1144953/10812500 : ℂ)/(lapse : ℂ), (8307/205000 : ℂ)/(lapse : ℂ), (13407/1937500 : ℂ)/(lapse : ℂ), (8307/205000 : ℂ)/(lapse : ℂ), (23301/3293750 : ℂ)/(lapse : ℂ), (13407/1937500 : ℂ)/(lapse : ℂ), (3834/25625 : ℂ)/(lapse : ℂ), (23301/6587500 : ℂ)/(lapse : ℂ), (23301/6587500 : ℂ)/(lapse : ℂ), (-16017/968750 : ℂ)/(lapse : ℂ), (1518632850854277/6768386327350000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (306197519224239/6768386327350000 : ℂ)/(lapse : ℂ), (7030536703911/33841931636750 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (29117323902519/135367726547000 : ℂ)/(lapse : ℂ), (-88506405025461/6768386327350000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (1486075050531477/6768386327350000 : ℂ)/(lapse : ℂ), (12834886509/3301651867000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (7030536703911/33841931636750 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (29117323902519/135367726547000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ), (12834886509/3301651867000 : ℂ)/(lapse : ℂ), (0 : ℂ)/(lapse : ℂ)] := by
    funext i
    fin_cases i
    · exact actual_scalar_row_0 dual
    · exact actual_scalar_row_1 dual
    · exact actual_scalar_row_2 dual
    · exact actual_scalar_row_3 dual
    · exact actual_scalar_row_4 dual
    · exact actual_scalar_row_5 dual
    · exact actual_scalar_row_6 dual
    · exact actual_scalar_row_7 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_10 dual
    · exact actual_scalar_row_11 dual
    · exact actual_scalar_row_12 dual
    · exact actual_scalar_row_13 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_16 dual
    · exact actual_scalar_row_17 dual
    · exact actual_scalar_row_18 dual
    · exact actual_scalar_row_19 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_22 dual
    · exact actual_scalar_row_23 dual
    · exact actual_scalar_row_24 dual
    · exact actual_scalar_row_25 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_28 dual
    · exact actual_scalar_row_29 dual
    · exact actual_scalar_row_30 dual
    · exact actual_scalar_row_31 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_34 dual
    · exact actual_scalar_row_35 dual
    · exact actual_scalar_row_36 dual
    · exact actual_scalar_row_37 dual
    · exact actual_scalar_row_38 dual
    · exact actual_scalar_row_39 dual
    · exact actual_scalar_row_40 dual
    · exact actual_scalar_row_41 dual
    · exact actual_scalar_row_42 dual
    · exact actual_scalar_row_43 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_46 dual
    · exact actual_scalar_row_47 dual
    · exact actual_scalar_row_48 dual
    · exact actual_scalar_row_49 dual
    · exact actual_scalar_row_50 dual
    · exact actual_scalar_row_51 dual
    · exact actual_scalar_row_52 dual
    · exact actual_scalar_row_53 dual
    · exact actual_scalar_row_54 dual
    · exact actual_scalar_row_55 dual
    · exact actual_scalar_row_56 dual
    · exact actual_scalar_row_57 dual
    · exact actual_scalar_row_58 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_60 dual
    · exact actual_scalar_row_61 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_63 dual
    · exact actual_scalar_row_64 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_66 dual
    · exact actual_scalar_row_67 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_71 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_73 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
    · exact actual_scalar_row_77 dual
    · simp [scalarRow,primalCurrentPoint,scalarBranch]
  rw [hf]
  norm_num [Fin.sum_univ_succ]
  ring

private theorem scalar_lapse_value :
    (150913290192423496344222314491299/81415930471860130022585251656250 : ℂ)/(lapse : ℂ) = canonicalScalar*(Real.sqrt 30 : ℂ) := by
  have hs : (Real.sqrt 30 : ℂ)^2 = 30 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 30 by norm_num)
  rw [ActualCandidateVertexValues.lapse_value]
  have hi : ((3/25 : ℂ)*(Real.sqrt 30 : ℂ))⁻¹ =
      (5/18 : ℂ)*(Real.sqrt 30 : ℂ) := by
    apply inv_eq_of_mul_eq_one_right
    calc
      _ = (1/30 : ℂ)*(Real.sqrt 30 : ℂ)^2 := by ring
      _ = 1 := by rw [hs]; norm_num
  rw [div_eq_mul_inv,hi]
  unfold canonicalScalar
  ring

/-- The original canonical inverse, including its original 79 component scaling,
contracted with the source-current table on each independent branch. -/
theorem actual_canonical_bra_contraction (dual : Bool) :
    (∑i : Fin 79,∑j : Fin 79,((-1/2 : ℂ)*axialInverse Complex.I 0 i j)*
      currentPoint dual i j) = canonicalScalar*(Real.sqrt 30 : ℂ) := by
  cases dual with
  | false =>
    change (∑i : Fin 79,scalarRow false i) = _
    rw [scalar_sum_value,scalar_lapse_value]
  | true =>
    simp only [currentPoint,if_pos]
    rw [Finset.sum_comm]
    change (∑i : Fin 79,scalarRow true i) = _
    rw [scalar_sum_value,scalar_lapse_value]

end LowEnergy.ActualCanonical79Imaginary
