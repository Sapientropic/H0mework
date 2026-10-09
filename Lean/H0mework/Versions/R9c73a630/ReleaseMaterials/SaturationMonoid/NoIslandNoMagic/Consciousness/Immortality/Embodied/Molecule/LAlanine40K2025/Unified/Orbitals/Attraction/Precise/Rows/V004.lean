import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_004_015
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_015_028
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_028_039
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_039_049
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_049_062
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_062_073
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_073_082
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_082_096
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V004_096_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_4 (j : Basis) (ordered : (4 : Basis) ≤ j) :
    |aoIntegral (4 : Basis) j - (recordedAttraction (4 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (4 : Basis) = ⟨4,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(4 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(4 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(4 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(4 : Basis) ≤ (3 : Basis) by decide) ordered)
  · convert vcell4_4_error using 1; norm_num
  · convert vcell4_5_error using 1; norm_num
  · convert vcell4_6_error using 1; norm_num
  · convert vcell4_7_error using 1; norm_num
  · convert vcell4_8_error using 1; norm_num
  · convert vcell4_9_error using 1; norm_num
  · convert vcell4_10_error using 1; norm_num
  · convert vcell4_11_error using 1; norm_num
  · convert vcell4_12_error using 1; norm_num
  · convert vcell4_13_error using 1; norm_num
  · convert vcell4_14_error using 1; norm_num
  · convert vcell4_15_error using 1; norm_num
  · convert vcell4_16_error using 1; norm_num
  · convert vcell4_17_error using 1; norm_num
  · convert vcell4_18_error using 1; norm_num
  · convert vcell4_19_error using 1; norm_num
  · convert vcell4_20_error using 1; norm_num
  · convert vcell4_21_error using 1; norm_num
  · convert vcell4_22_error using 1; norm_num
  · convert vcell4_23_error using 1; norm_num
  · convert vcell4_24_error using 1; norm_num
  · convert vcell4_25_error using 1; norm_num
  · convert vcell4_26_error using 1; norm_num
  · convert vcell4_27_error using 1; norm_num
  · convert vcell4_28_error using 1; norm_num
  · convert vcell4_29_error using 1; norm_num
  · convert vcell4_30_error using 1; norm_num
  · convert vcell4_31_error using 1; norm_num
  · convert vcell4_32_error using 1; norm_num
  · convert vcell4_33_error using 1; norm_num
  · convert vcell4_34_error using 1; norm_num
  · convert vcell4_35_error using 1; norm_num
  · convert vcell4_36_error using 1; norm_num
  · convert vcell4_37_error using 1; norm_num
  · convert vcell4_38_error using 1; norm_num
  · convert vcell4_39_error using 1; norm_num
  · convert vcell4_40_error using 1; norm_num
  · convert vcell4_41_error using 1; norm_num
  · convert vcell4_42_error using 1; norm_num
  · convert vcell4_43_error using 1; norm_num
  · convert vcell4_44_error using 1; norm_num
  · convert vcell4_45_error using 1; norm_num
  · convert vcell4_46_error using 1; norm_num
  · convert vcell4_47_error using 1; norm_num
  · convert vcell4_48_error using 1; norm_num
  · convert vcell4_49_error using 1; norm_num
  · convert vcell4_50_error using 1; norm_num
  · convert vcell4_51_error using 1; norm_num
  · convert vcell4_52_error using 1; norm_num
  · convert vcell4_53_error using 1; norm_num
  · convert vcell4_54_error using 1; norm_num
  · convert vcell4_55_error using 1; norm_num
  · convert vcell4_56_error using 1; norm_num
  · convert vcell4_57_error using 1; norm_num
  · convert vcell4_58_error using 1; norm_num
  · convert vcell4_59_error using 1; norm_num
  · convert vcell4_60_error using 1; norm_num
  · convert vcell4_61_error using 1; norm_num
  · convert vcell4_62_error using 1; norm_num
  · convert vcell4_63_error using 1; norm_num
  · convert vcell4_64_error using 1; norm_num
  · convert vcell4_65_error using 1; norm_num
  · convert vcell4_66_error using 1; norm_num
  · convert vcell4_67_error using 1; norm_num
  · convert vcell4_68_error using 1; norm_num
  · convert vcell4_69_error using 1; norm_num
  · convert vcell4_70_error using 1; norm_num
  · convert vcell4_71_error using 1; norm_num
  · convert vcell4_72_error using 1; norm_num
  · convert vcell4_73_error using 1; norm_num
  · convert vcell4_74_error using 1; norm_num
  · convert vcell4_75_error using 1; norm_num
  · convert vcell4_76_error using 1; norm_num
  · convert vcell4_77_error using 1; norm_num
  · convert vcell4_78_error using 1; norm_num
  · convert vcell4_79_error using 1; norm_num
  · convert vcell4_80_error using 1; norm_num
  · convert vcell4_81_error using 1; norm_num
  · convert vcell4_82_error using 1; norm_num
  · convert vcell4_83_error using 1; norm_num
  · convert vcell4_84_error using 1; norm_num
  · convert vcell4_85_error using 1; norm_num
  · convert vcell4_86_error using 1; norm_num
  · convert vcell4_87_error using 1; norm_num
  · convert vcell4_88_error using 1; norm_num
  · convert vcell4_89_error using 1; norm_num
  · convert vcell4_90_error using 1; norm_num
  · convert vcell4_91_error using 1; norm_num
  · convert vcell4_92_error using 1; norm_num
  · convert vcell4_93_error using 1; norm_num
  · convert vcell4_94_error using 1; norm_num
  · convert vcell4_95_error using 1; norm_num
  · convert vcell4_96_error using 1; norm_num
  · convert vcell4_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
