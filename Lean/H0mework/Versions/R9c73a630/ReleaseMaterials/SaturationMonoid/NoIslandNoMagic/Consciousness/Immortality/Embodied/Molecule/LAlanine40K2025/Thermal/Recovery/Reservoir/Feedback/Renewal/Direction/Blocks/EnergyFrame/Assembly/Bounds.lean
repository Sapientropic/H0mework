import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Matrix
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.ListBounds

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface
open scoped Matrix BigOperators

theorem all_gram_errors (i : Basis) : (((Rows.rowAt gramRows i).zip
    (List.ofFn (fun j : Basis => if j=i then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by
  fin_cases i
  · exact gram_error_0
  · exact gram_error_1
  · exact gram_error_2
  · exact gram_error_3
  · exact gram_error_4
  · exact gram_error_5
  · exact gram_error_6
  · exact gram_error_7
  · exact gram_error_8
  · exact gram_error_9
  · exact gram_error_10
  · exact gram_error_11
  · exact gram_error_12
  · exact gram_error_13
  · exact gram_error_14
  · exact gram_error_15
  · exact gram_error_16
  · exact gram_error_17
  · exact gram_error_18
  · exact gram_error_19
  · exact gram_error_20
  · exact gram_error_21
  · exact gram_error_22
  · exact gram_error_23
  · exact gram_error_24
  · exact gram_error_25
  · exact gram_error_26
  · exact gram_error_27
  · exact gram_error_28
  · exact gram_error_29
  · exact gram_error_30
  · exact gram_error_31
  · exact gram_error_32
  · exact gram_error_33
  · exact gram_error_34
  · exact gram_error_35
  · exact gram_error_36
  · exact gram_error_37
  · exact gram_error_38
  · exact gram_error_39
  · exact gram_error_40
  · exact gram_error_41
  · exact gram_error_42
  · exact gram_error_43
  · exact gram_error_44
  · exact gram_error_45
  · exact gram_error_46
  · exact gram_error_47
  · exact gram_error_48
  · exact gram_error_49
  · exact gram_error_50
  · exact gram_error_51
  · exact gram_error_52
  · exact gram_error_53
  · exact gram_error_54
  · exact gram_error_55
  · exact gram_error_56
  · exact gram_error_57
  · exact gram_error_58
  · exact gram_error_59
  · exact gram_error_60
  · exact gram_error_61
  · exact gram_error_62
  · exact gram_error_63
  · exact gram_error_64
  · exact gram_error_65
  · exact gram_error_66
  · exact gram_error_67
  · exact gram_error_68
  · exact gram_error_69
  · exact gram_error_70
  · exact gram_error_71
  · exact gram_error_72
  · exact gram_error_73
  · exact gram_error_74
  · exact gram_error_75
  · exact gram_error_76
  · exact gram_error_77
  · exact gram_error_78
  · exact gram_error_79
  · exact gram_error_80
  · exact gram_error_81
  · exact gram_error_82
  · exact gram_error_83
  · exact gram_error_84
  · exact gram_error_85
  · exact gram_error_86
  · exact gram_error_87
  · exact gram_error_88
  · exact gram_error_89
  · exact gram_error_90
  · exact gram_error_91
  · exact gram_error_92
  · exact gram_error_93
  · exact gram_error_94
  · exact gram_error_95
  · exact gram_error_96
  · exact gram_error_97

theorem all_eigen_errors (i : Basis) : ((Rows.rowAt residualColumns i).map abs).all (· ≤ 3*10^16) = true := by
  fin_cases i
  · exact eigen_error_0
  · exact eigen_error_1
  · exact eigen_error_2
  · exact eigen_error_3
  · exact eigen_error_4
  · exact eigen_error_5
  · exact eigen_error_6
  · exact eigen_error_7
  · exact eigen_error_8
  · exact eigen_error_9
  · exact eigen_error_10
  · exact eigen_error_11
  · exact eigen_error_12
  · exact eigen_error_13
  · exact eigen_error_14
  · exact eigen_error_15
  · exact eigen_error_16
  · exact eigen_error_17
  · exact eigen_error_18
  · exact eigen_error_19
  · exact eigen_error_20
  · exact eigen_error_21
  · exact eigen_error_22
  · exact eigen_error_23
  · exact eigen_error_24
  · exact eigen_error_25
  · exact eigen_error_26
  · exact eigen_error_27
  · exact eigen_error_28
  · exact eigen_error_29
  · exact eigen_error_30
  · exact eigen_error_31
  · exact eigen_error_32
  · exact eigen_error_33
  · exact eigen_error_34
  · exact eigen_error_35
  · exact eigen_error_36
  · exact eigen_error_37
  · exact eigen_error_38
  · exact eigen_error_39
  · exact eigen_error_40
  · exact eigen_error_41
  · exact eigen_error_42
  · exact eigen_error_43
  · exact eigen_error_44
  · exact eigen_error_45
  · exact eigen_error_46
  · exact eigen_error_47
  · exact eigen_error_48
  · exact eigen_error_49
  · exact eigen_error_50
  · exact eigen_error_51
  · exact eigen_error_52
  · exact eigen_error_53
  · exact eigen_error_54
  · exact eigen_error_55
  · exact eigen_error_56
  · exact eigen_error_57
  · exact eigen_error_58
  · exact eigen_error_59
  · exact eigen_error_60
  · exact eigen_error_61
  · exact eigen_error_62
  · exact eigen_error_63
  · exact eigen_error_64
  · exact eigen_error_65
  · exact eigen_error_66
  · exact eigen_error_67
  · exact eigen_error_68
  · exact eigen_error_69
  · exact eigen_error_70
  · exact eigen_error_71
  · exact eigen_error_72
  · exact eigen_error_73
  · exact eigen_error_74
  · exact eigen_error_75
  · exact eigen_error_76
  · exact eigen_error_77
  · exact eigen_error_78
  · exact eigen_error_79
  · exact eigen_error_80
  · exact eigen_error_81
  · exact eigen_error_82
  · exact eigen_error_83
  · exact eigen_error_84
  · exact eigen_error_85
  · exact eigen_error_86
  · exact eigen_error_87
  · exact eigen_error_88
  · exact eigen_error_89
  · exact eigen_error_90
  · exact eigen_error_91
  · exact eigen_error_92
  · exact eigen_error_93
  · exact eigen_error_94
  · exact eigen_error_95
  · exact eigen_error_96
  · exact eigen_error_97

theorem all_eigen_residuals (i : Basis) : Rows.rowAt residualColumns i =
    ((Rows.rowAt appliedColumns i).zip (Rows.rowAt frameColumns i)).map
      (fun pair => pair.1-pair.2*energies[i.val]!) := by
  fin_cases i
  · exact eigen_residual_0
  · exact eigen_residual_1
  · exact eigen_residual_2
  · exact eigen_residual_3
  · exact eigen_residual_4
  · exact eigen_residual_5
  · exact eigen_residual_6
  · exact eigen_residual_7
  · exact eigen_residual_8
  · exact eigen_residual_9
  · exact eigen_residual_10
  · exact eigen_residual_11
  · exact eigen_residual_12
  · exact eigen_residual_13
  · exact eigen_residual_14
  · exact eigen_residual_15
  · exact eigen_residual_16
  · exact eigen_residual_17
  · exact eigen_residual_18
  · exact eigen_residual_19
  · exact eigen_residual_20
  · exact eigen_residual_21
  · exact eigen_residual_22
  · exact eigen_residual_23
  · exact eigen_residual_24
  · exact eigen_residual_25
  · exact eigen_residual_26
  · exact eigen_residual_27
  · exact eigen_residual_28
  · exact eigen_residual_29
  · exact eigen_residual_30
  · exact eigen_residual_31
  · exact eigen_residual_32
  · exact eigen_residual_33
  · exact eigen_residual_34
  · exact eigen_residual_35
  · exact eigen_residual_36
  · exact eigen_residual_37
  · exact eigen_residual_38
  · exact eigen_residual_39
  · exact eigen_residual_40
  · exact eigen_residual_41
  · exact eigen_residual_42
  · exact eigen_residual_43
  · exact eigen_residual_44
  · exact eigen_residual_45
  · exact eigen_residual_46
  · exact eigen_residual_47
  · exact eigen_residual_48
  · exact eigen_residual_49
  · exact eigen_residual_50
  · exact eigen_residual_51
  · exact eigen_residual_52
  · exact eigen_residual_53
  · exact eigen_residual_54
  · exact eigen_residual_55
  · exact eigen_residual_56
  · exact eigen_residual_57
  · exact eigen_residual_58
  · exact eigen_residual_59
  · exact eigen_residual_60
  · exact eigen_residual_61
  · exact eigen_residual_62
  · exact eigen_residual_63
  · exact eigen_residual_64
  · exact eigen_residual_65
  · exact eigen_residual_66
  · exact eigen_residual_67
  · exact eigen_residual_68
  · exact eigen_residual_69
  · exact eigen_residual_70
  · exact eigen_residual_71
  · exact eigen_residual_72
  · exact eigen_residual_73
  · exact eigen_residual_74
  · exact eigen_residual_75
  · exact eigen_residual_76
  · exact eigen_residual_77
  · exact eigen_residual_78
  · exact eigen_residual_79
  · exact eigen_residual_80
  · exact eigen_residual_81
  · exact eigen_residual_82
  · exact eigen_residual_83
  · exact eigen_residual_84
  · exact eigen_residual_85
  · exact eigen_residual_86
  · exact eigen_residual_87
  · exact eigen_residual_88
  · exact eigen_residual_89
  · exact eigen_residual_90
  · exact eigen_residual_91
  · exact eigen_residual_92
  · exact eigen_residual_93
  · exact eigen_residual_94
  · exact eigen_residual_95
  · exact eigen_residual_96
  · exact eigen_residual_97

theorem gram_entry_bound (i j : Basis) : |gram i j-(if j=i then (10^30 : Int) else 0)| ≤ 3*10^15 := by
  have bound := all_difference_bound (Rows.rowAt gramRows i)
    (List.ofFn (fun j : Basis => if j=i then (10^30 : Int) else 0)) (gramRows_lengths i)
    (by simp) (3*10^15) (all_gram_errors i) j
  have readOfFn {n : Nat} (f : Fin n → Int) (j : Fin n) : Rows.read (List.ofFn f) j = f j := by
    unfold Rows.read
    rw [getElem!_pos (List.ofFn f) j.val (by simpa only [List.length_ofFn] using j.isLt)]
    simp only [List.getElem_ofFn,Fin.eta]
  rw [readOfFn] at bound
  exact bound

theorem residual_entry_bound (i j : Basis) :
    |Rows.read (Rows.rowAt residualColumns j) i| ≤ 3*10^16 :=
  all_abs_bound _ (residualColumns_lengths j) _ (all_eigen_errors j) i

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
