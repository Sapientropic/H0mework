import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V002_002_039
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V002_039_075
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V002_075_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_2 (j : Basis) (ordered : (2 : Basis) ≤ j) :
    |aoIntegral (2 : Basis) j - (recordedAttraction (2 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (2 : Basis) = ⟨2,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(2 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(2 : Basis) ≤ (1 : Basis) by decide) ordered)
  · convert vcell2_2_error using 1; norm_num
  · convert vcell2_3_error using 1; norm_num
  · convert vcell2_4_error using 1; norm_num
  · convert vcell2_5_error using 1; norm_num
  · convert vcell2_6_error using 1; norm_num
  · convert vcell2_7_error using 1; norm_num
  · convert vcell2_8_error using 1; norm_num
  · convert vcell2_9_error using 1; norm_num
  · convert vcell2_10_error using 1; norm_num
  · convert vcell2_11_error using 1; norm_num
  · convert vcell2_12_error using 1; norm_num
  · convert vcell2_13_error using 1; norm_num
  · convert vcell2_14_error using 1; norm_num
  · convert vcell2_15_error using 1; norm_num
  · convert vcell2_16_error using 1; norm_num
  · convert vcell2_17_error using 1; norm_num
  · convert vcell2_18_error using 1; norm_num
  · convert vcell2_19_error using 1; norm_num
  · convert vcell2_20_error using 1; norm_num
  · convert vcell2_21_error using 1; norm_num
  · convert vcell2_22_error using 1; norm_num
  · convert vcell2_23_error using 1; norm_num
  · convert vcell2_24_error using 1; norm_num
  · convert vcell2_25_error using 1; norm_num
  · convert vcell2_26_error using 1; norm_num
  · convert vcell2_27_error using 1; norm_num
  · convert vcell2_28_error using 1; norm_num
  · convert vcell2_29_error using 1; norm_num
  · convert vcell2_30_error using 1; norm_num
  · convert vcell2_31_error using 1; norm_num
  · convert vcell2_32_error using 1; norm_num
  · convert vcell2_33_error using 1; norm_num
  · convert vcell2_34_error using 1; norm_num
  · convert vcell2_35_error using 1; norm_num
  · convert vcell2_36_error using 1; norm_num
  · convert vcell2_37_error using 1; norm_num
  · convert vcell2_38_error using 1; norm_num
  · convert vcell2_39_error using 1; norm_num
  · convert vcell2_40_error using 1; norm_num
  · convert vcell2_41_error using 1; norm_num
  · convert vcell2_42_error using 1; norm_num
  · convert vcell2_43_error using 1; norm_num
  · convert vcell2_44_error using 1; norm_num
  · convert vcell2_45_error using 1; norm_num
  · convert vcell2_46_error using 1; norm_num
  · convert vcell2_47_error using 1; norm_num
  · convert vcell2_48_error using 1; norm_num
  · convert vcell2_49_error using 1; norm_num
  · convert vcell2_50_error using 1; norm_num
  · convert vcell2_51_error using 1; norm_num
  · convert vcell2_52_error using 1; norm_num
  · convert vcell2_53_error using 1; norm_num
  · convert vcell2_54_error using 1; norm_num
  · convert vcell2_55_error using 1; norm_num
  · convert vcell2_56_error using 1; norm_num
  · convert vcell2_57_error using 1; norm_num
  · convert vcell2_58_error using 1; norm_num
  · convert vcell2_59_error using 1; norm_num
  · convert vcell2_60_error using 1; norm_num
  · convert vcell2_61_error using 1; norm_num
  · convert vcell2_62_error using 1; norm_num
  · convert vcell2_63_error using 1; norm_num
  · convert vcell2_64_error using 1; norm_num
  · convert vcell2_65_error using 1; norm_num
  · convert vcell2_66_error using 1; norm_num
  · convert vcell2_67_error using 1; norm_num
  · convert vcell2_68_error using 1; norm_num
  · convert vcell2_69_error using 1; norm_num
  · convert vcell2_70_error using 1; norm_num
  · convert vcell2_71_error using 1; norm_num
  · convert vcell2_72_error using 1; norm_num
  · convert vcell2_73_error using 1; norm_num
  · convert vcell2_74_error using 1; norm_num
  · convert vcell2_75_error using 1; norm_num
  · convert vcell2_76_error using 1; norm_num
  · convert vcell2_77_error using 1; norm_num
  · convert vcell2_78_error using 1; norm_num
  · convert vcell2_79_error using 1; norm_num
  · convert vcell2_80_error using 1; norm_num
  · convert vcell2_81_error using 1; norm_num
  · convert vcell2_82_error using 1; norm_num
  · convert vcell2_83_error using 1; norm_num
  · convert vcell2_84_error using 1; norm_num
  · convert vcell2_85_error using 1; norm_num
  · convert vcell2_86_error using 1; norm_num
  · convert vcell2_87_error using 1; norm_num
  · convert vcell2_88_error using 1; norm_num
  · convert vcell2_89_error using 1; norm_num
  · convert vcell2_90_error using 1; norm_num
  · convert vcell2_91_error using 1; norm_num
  · convert vcell2_92_error using 1; norm_num
  · convert vcell2_93_error using 1; norm_num
  · convert vcell2_94_error using 1; norm_num
  · convert vcell2_95_error using 1; norm_num
  · convert vcell2_96_error using 1; norm_num
  · convert vcell2_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
