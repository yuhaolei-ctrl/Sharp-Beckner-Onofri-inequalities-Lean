import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0290
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0290
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2320 : minorantGammaCheck GammaPanel2320.certificate 1621=true := by decide +kernel
noncomputable def cell2320 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2320.certificate 1621 accepted2320
theorem accepted2321 : minorantGammaCheck GammaPanel2321.certificate 1621=true := by decide +kernel
noncomputable def cell2321 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2321.certificate 1621 accepted2321
theorem accepted2322 : minorantGammaCheck GammaPanel2322.certificate 1621=true := by decide +kernel
noncomputable def cell2322 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2322.certificate 1621 accepted2322
theorem accepted2323 : minorantGammaCheck GammaPanel2323.certificate 1621=true := by decide +kernel
noncomputable def cell2323 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2323.certificate 1621 accepted2323
theorem accepted2324 : minorantGammaCheck GammaPanel2324.certificate 1621=true := by decide +kernel
noncomputable def cell2324 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2324.certificate 1621 accepted2324
theorem accepted2325 : minorantGammaCheck GammaPanel2325.certificate 1621=true := by decide +kernel
noncomputable def cell2325 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2325.certificate 1621 accepted2325
theorem accepted2326 : minorantGammaCheck GammaPanel2326.certificate 1621=true := by decide +kernel
noncomputable def cell2326 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2326.certificate 1621 accepted2326
theorem accepted2327 : minorantGammaCheck GammaPanel2327.certificate 1621=true := by decide +kernel
noncomputable def cell2327 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2327.certificate 1621 accepted2327
noncomputable def cells : List CertifiedMinorantCell := [cell2320, cell2321, cell2322, cell2323, cell2324, cell2325, cell2326, cell2327]
theorem chainAccepted : minorantChainCheck (4921/5000) (197/200) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4921/5000) (197/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0290
