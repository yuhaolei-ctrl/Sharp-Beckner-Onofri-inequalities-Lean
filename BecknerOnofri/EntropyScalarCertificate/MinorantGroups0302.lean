module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0302

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0302
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2416 : minorantGammaCheck GammaPanel2416.certificate 1621=true := by decide +kernel
noncomputable def cell2416 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2416.certificate 1621 accepted2416
theorem accepted2417 : minorantGammaCheck GammaPanel2417.certificate 1621=true := by decide +kernel
noncomputable def cell2417 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2417.certificate 1621 accepted2417
theorem accepted2418 : minorantGammaCheck GammaPanel2418.certificate 1621=true := by decide +kernel
noncomputable def cell2418 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2418.certificate 1621 accepted2418
theorem accepted2419 : minorantGammaCheck GammaPanel2419.certificate 1621=true := by decide +kernel
noncomputable def cell2419 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2419.certificate 1621 accepted2419
theorem accepted2420 : minorantGammaCheck GammaPanel2420.certificate 1621=true := by decide +kernel
noncomputable def cell2420 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2420.certificate 1621 accepted2420
theorem accepted2421 : minorantGammaCheck GammaPanel2421.certificate 1621=true := by decide +kernel
noncomputable def cell2421 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2421.certificate 1621 accepted2421
theorem accepted2422 : minorantGammaCheck GammaPanel2422.certificate 1621=true := by decide +kernel
noncomputable def cell2422 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2422.certificate 1621 accepted2422
theorem accepted2423 : minorantGammaCheck GammaPanel2423.certificate 1621=true := by decide +kernel
noncomputable def cell2423 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2423.certificate 1621 accepted2423
noncomputable def cells : List CertifiedMinorantCell := [cell2416, cell2417, cell2418, cell2419, cell2420, cell2421, cell2422, cell2423]
theorem chainAccepted : minorantChainCheck (24769/25000) (24773/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24769/25000) (24773/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0302
