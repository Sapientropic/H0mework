import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows0000
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows0512
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows1024
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows1536
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows2048
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows2560
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows3072
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows3584
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows4096
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Blocks.Rows4608

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin

theorem all_target_rows_certified (address : Fin 4851) :
    targetRowCertified address.val := by
  have bound : address.val < 4851 := address.isLt
  by_cases h0 : address.val < 512
  · have h := rows0000 ⟨address.val - 0, by omega⟩
    have eqn : 0 + (address.val - 0) = address.val := by omega
    simpa only [eqn] using h
  ·
    by_cases h1 : address.val < 1024
    · have h := rows0512 ⟨address.val - 512, by omega⟩
      have eqn : 512 + (address.val - 512) = address.val := by omega
      simpa only [eqn] using h
    ·
      by_cases h2 : address.val < 1536
      · have h := rows1024 ⟨address.val - 1024, by omega⟩
        have eqn : 1024 + (address.val - 1024) = address.val := by omega
        simpa only [eqn] using h
      ·
        by_cases h3 : address.val < 2048
        · have h := rows1536 ⟨address.val - 1536, by omega⟩
          have eqn : 1536 + (address.val - 1536) = address.val := by omega
          simpa only [eqn] using h
        ·
          by_cases h4 : address.val < 2560
          · have h := rows2048 ⟨address.val - 2048, by omega⟩
            have eqn : 2048 + (address.val - 2048) = address.val := by omega
            simpa only [eqn] using h
          ·
            by_cases h5 : address.val < 3072
            · have h := rows2560 ⟨address.val - 2560, by omega⟩
              have eqn : 2560 + (address.val - 2560) = address.val := by omega
              simpa only [eqn] using h
            ·
              by_cases h6 : address.val < 3584
              · have h := rows3072 ⟨address.val - 3072, by omega⟩
                have eqn : 3072 + (address.val - 3072) = address.val := by omega
                simpa only [eqn] using h
              ·
                by_cases h7 : address.val < 4096
                · have h := rows3584 ⟨address.val - 3584, by omega⟩
                  have eqn : 3584 + (address.val - 3584) = address.val := by omega
                  simpa only [eqn] using h
                ·
                  by_cases h8 : address.val < 4608
                  · have h := rows4096 ⟨address.val - 4096, by omega⟩
                    have eqn : 4096 + (address.val - 4096) = address.val := by omega
                    simpa only [eqn] using h
                  ·
                    have h := rows4608 ⟨address.val - 4608, by omega⟩
                    have eqn : 4608 + (address.val - 4608) = address.val := by omega
                    simpa only [eqn] using h

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
