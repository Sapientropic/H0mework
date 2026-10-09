import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_005_017
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_017_028
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_028_039
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_039_049
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_049_062
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_062_073
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_073_082
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_082_096
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V005_096_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_5 (j : Basis) (ordered : (5 : Basis) ≤ j) :
    |aoIntegral (5 : Basis) j - (recordedAttraction (5 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (5 : Basis) = ⟨5,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(5 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(5 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(5 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(5 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(5 : Basis) ≤ (4 : Basis) by decide) ordered)
  · convert vcell5_5_error using 1; norm_num
  · convert vcell5_6_error using 1; norm_num
  · convert vcell5_7_error using 1; norm_num
  · convert vcell5_8_error using 1; norm_num
  · convert vcell5_9_error using 1; norm_num
  · convert vcell5_10_error using 1; norm_num
  · convert vcell5_11_error using 1; norm_num
  · convert vcell5_12_error using 1; norm_num
  · convert vcell5_13_error using 1; norm_num
  · convert vcell5_14_error using 1; norm_num
  · convert vcell5_15_error using 1; norm_num
  · convert vcell5_16_error using 1; norm_num
  · convert vcell5_17_error using 1; norm_num
  · convert vcell5_18_error using 1; norm_num
  · convert vcell5_19_error using 1; norm_num
  · convert vcell5_20_error using 1; norm_num
  · convert vcell5_21_error using 1; norm_num
  · convert vcell5_22_error using 1; norm_num
  · convert vcell5_23_error using 1; norm_num
  · convert vcell5_24_error using 1; norm_num
  · convert vcell5_25_error using 1; norm_num
  · convert vcell5_26_error using 1; norm_num
  · convert vcell5_27_error using 1; norm_num
  · convert vcell5_28_error using 1; norm_num
  · convert vcell5_29_error using 1; norm_num
  · convert vcell5_30_error using 1; norm_num
  · convert vcell5_31_error using 1; norm_num
  · convert vcell5_32_error using 1; norm_num
  · convert vcell5_33_error using 1; norm_num
  · convert vcell5_34_error using 1; norm_num
  · convert vcell5_35_error using 1; norm_num
  · convert vcell5_36_error using 1; norm_num
  · convert vcell5_37_error using 1; norm_num
  · convert vcell5_38_error using 1; norm_num
  · convert vcell5_39_error using 1; norm_num
  · convert vcell5_40_error using 1; norm_num
  · convert vcell5_41_error using 1; norm_num
  · convert vcell5_42_error using 1; norm_num
  · convert vcell5_43_error using 1; norm_num
  · convert vcell5_44_error using 1; norm_num
  · convert vcell5_45_error using 1; norm_num
  · convert vcell5_46_error using 1; norm_num
  · convert vcell5_47_error using 1; norm_num
  · convert vcell5_48_error using 1; norm_num
  · convert vcell5_49_error using 1; norm_num
  · convert vcell5_50_error using 1; norm_num
  · convert vcell5_51_error using 1; norm_num
  · convert vcell5_52_error using 1; norm_num
  · convert vcell5_53_error using 1; norm_num
  · convert vcell5_54_error using 1; norm_num
  · convert vcell5_55_error using 1; norm_num
  · convert vcell5_56_error using 1; norm_num
  · convert vcell5_57_error using 1; norm_num
  · convert vcell5_58_error using 1; norm_num
  · convert vcell5_59_error using 1; norm_num
  · convert vcell5_60_error using 1; norm_num
  · convert vcell5_61_error using 1; norm_num
  · convert vcell5_62_error using 1; norm_num
  · convert vcell5_63_error using 1; norm_num
  · convert vcell5_64_error using 1; norm_num
  · convert vcell5_65_error using 1; norm_num
  · convert vcell5_66_error using 1; norm_num
  · convert vcell5_67_error using 1; norm_num
  · convert vcell5_68_error using 1; norm_num
  · convert vcell5_69_error using 1; norm_num
  · convert vcell5_70_error using 1; norm_num
  · convert vcell5_71_error using 1; norm_num
  · convert vcell5_72_error using 1; norm_num
  · convert vcell5_73_error using 1; norm_num
  · convert vcell5_74_error using 1; norm_num
  · convert vcell5_75_error using 1; norm_num
  · convert vcell5_76_error using 1; norm_num
  · convert vcell5_77_error using 1; norm_num
  · convert vcell5_78_error using 1; norm_num
  · convert vcell5_79_error using 1; norm_num
  · convert vcell5_80_error using 1; norm_num
  · convert vcell5_81_error using 1; norm_num
  · convert vcell5_82_error using 1; norm_num
  · convert vcell5_83_error using 1; norm_num
  · convert vcell5_84_error using 1; norm_num
  · convert vcell5_85_error using 1; norm_num
  · convert vcell5_86_error using 1; norm_num
  · convert vcell5_87_error using 1; norm_num
  · convert vcell5_88_error using 1; norm_num
  · convert vcell5_89_error using 1; norm_num
  · convert vcell5_90_error using 1; norm_num
  · convert vcell5_91_error using 1; norm_num
  · convert vcell5_92_error using 1; norm_num
  · convert vcell5_93_error using 1; norm_num
  · convert vcell5_94_error using 1; norm_num
  · convert vcell5_95_error using 1; norm_num
  · convert vcell5_96_error using 1; norm_num
  · convert vcell5_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
