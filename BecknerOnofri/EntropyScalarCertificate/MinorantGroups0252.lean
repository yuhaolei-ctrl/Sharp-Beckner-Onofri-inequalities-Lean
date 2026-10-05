import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0252
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0252
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2016 : minorantGammaCheck GammaPanel2016.certificate 1621=true := by decide +kernel
noncomputable def cell2016 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2016.certificate 1621 accepted2016
theorem accepted2017 : minorantGammaCheck GammaPanel2017.certificate 1621=true := by decide +kernel
noncomputable def cell2017 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2017.certificate 1621 accepted2017
theorem accepted2018 : minorantGammaCheck GammaPanel2018.certificate 1621=true := by decide +kernel
noncomputable def cell2018 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2018.certificate 1621 accepted2018
theorem accepted2019 : minorantGammaCheck GammaPanel2019.certificate 1621=true := by decide +kernel
noncomputable def cell2019 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2019.certificate 1621 accepted2019
theorem accepted2020 : minorantGammaCheck GammaPanel2020.certificate 1621=true := by decide +kernel
noncomputable def cell2020 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2020.certificate 1621 accepted2020
theorem accepted2021 : minorantGammaCheck GammaPanel2021.certificate 1621=true := by decide +kernel
noncomputable def cell2021 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2021.certificate 1621 accepted2021
theorem accepted2022 : minorantGammaCheck GammaPanel2022.certificate 1621=true := by decide +kernel
noncomputable def cell2022 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2022.certificate 1621 accepted2022
theorem accepted2023 : minorantGammaCheck GammaPanel2023.certificate 1621=true := by decide +kernel
noncomputable def cell2023 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2023.certificate 1621 accepted2023
noncomputable def cells : List CertifiedMinorantCell := [cell2016, cell2017, cell2018, cell2019, cell2020, cell2021, cell2022, cell2023]
theorem chainAccepted : minorantChainCheck (4769/5000) (4773/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4769/5000) (4773/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0252
