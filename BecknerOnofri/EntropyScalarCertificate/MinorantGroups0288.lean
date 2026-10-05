module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0288

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0288
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2304 : minorantGammaCheck GammaPanel2304.certificate 1621=true := by decide +kernel
noncomputable def cell2304 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2304.certificate 1621 accepted2304
theorem accepted2305 : minorantGammaCheck GammaPanel2305.certificate 1621=true := by decide +kernel
noncomputable def cell2305 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2305.certificate 1621 accepted2305
theorem accepted2306 : minorantGammaCheck GammaPanel2306.certificate 1621=true := by decide +kernel
noncomputable def cell2306 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2306.certificate 1621 accepted2306
theorem accepted2307 : minorantGammaCheck GammaPanel2307.certificate 1621=true := by decide +kernel
noncomputable def cell2307 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2307.certificate 1621 accepted2307
theorem accepted2308 : minorantGammaCheck GammaPanel2308.certificate 1621=true := by decide +kernel
noncomputable def cell2308 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2308.certificate 1621 accepted2308
theorem accepted2309 : minorantGammaCheck GammaPanel2309.certificate 1621=true := by decide +kernel
noncomputable def cell2309 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2309.certificate 1621 accepted2309
theorem accepted2310 : minorantGammaCheck GammaPanel2310.certificate 1621=true := by decide +kernel
noncomputable def cell2310 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2310.certificate 1621 accepted2310
theorem accepted2311 : minorantGammaCheck GammaPanel2311.certificate 1621=true := by decide +kernel
noncomputable def cell2311 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2311.certificate 1621 accepted2311
noncomputable def cells : List CertifiedMinorantCell := [cell2304, cell2305, cell2306, cell2307, cell2308, cell2309, cell2310, cell2311]
theorem chainAccepted : minorantChainCheck (4913/5000) (4917/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4913/5000) (4917/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0288
