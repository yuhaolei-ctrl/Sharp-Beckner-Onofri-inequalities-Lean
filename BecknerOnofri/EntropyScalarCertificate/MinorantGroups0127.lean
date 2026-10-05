module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0127

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0127
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1016 : minorantGammaCheck GammaPanel1016.certificate 914=true := by decide +kernel
noncomputable def cell1016 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1016.certificate 914 accepted1016
theorem accepted1017 : minorantGammaCheck GammaPanel1017.certificate 915=true := by decide +kernel
noncomputable def cell1017 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1017.certificate 915 accepted1017
theorem accepted1018 : minorantGammaCheck GammaPanel1018.certificate 916=true := by decide +kernel
noncomputable def cell1018 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1018.certificate 916 accepted1018
theorem accepted1019 : minorantGammaCheck GammaPanel1019.certificate 917=true := by decide +kernel
noncomputable def cell1019 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1019.certificate 917 accepted1019
theorem accepted1020 : minorantGammaCheck GammaPanel1020.certificate 918=true := by decide +kernel
noncomputable def cell1020 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1020.certificate 918 accepted1020
theorem accepted1021 : minorantGammaCheck GammaPanel1021.certificate 919=true := by decide +kernel
noncomputable def cell1021 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1021.certificate 919 accepted1021
theorem accepted1022 : minorantGammaCheck GammaPanel1022.certificate 920=true := by decide +kernel
noncomputable def cell1022 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1022.certificate 920 accepted1022
theorem accepted1023 : minorantGammaCheck GammaPanel1023.certificate 921=true := by decide +kernel
noncomputable def cell1023 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1023.certificate 921 accepted1023
noncomputable def cells : List CertifiedMinorantCell := [cell1016, cell1017, cell1018, cell1019, cell1020, cell1021, cell1022, cell1023]
theorem chainAccepted : minorantChainCheck (249/500) (253/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (249/500) (253/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0127
