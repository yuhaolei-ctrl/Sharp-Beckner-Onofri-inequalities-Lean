module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0293

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0293
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2344 : minorantGammaCheck GammaPanel2344.certificate 1621=true := by decide +kernel
noncomputable def cell2344 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2344.certificate 1621 accepted2344
theorem accepted2345 : minorantGammaCheck GammaPanel2345.certificate 1621=true := by decide +kernel
noncomputable def cell2345 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2345.certificate 1621 accepted2345
theorem accepted2346 : minorantGammaCheck GammaPanel2346.certificate 1621=true := by decide +kernel
noncomputable def cell2346 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2346.certificate 1621 accepted2346
theorem accepted2347 : minorantGammaCheck GammaPanel2347.certificate 1621=true := by decide +kernel
noncomputable def cell2347 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2347.certificate 1621 accepted2347
theorem accepted2348 : minorantGammaCheck GammaPanel2348.certificate 1621=true := by decide +kernel
noncomputable def cell2348 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2348.certificate 1621 accepted2348
theorem accepted2349 : minorantGammaCheck GammaPanel2349.certificate 1621=true := by decide +kernel
noncomputable def cell2349 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2349.certificate 1621 accepted2349
theorem accepted2350 : minorantGammaCheck GammaPanel2350.certificate 1621=true := by decide +kernel
noncomputable def cell2350 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2350.certificate 1621 accepted2350
theorem accepted2351 : minorantGammaCheck GammaPanel2351.certificate 1621=true := by decide +kernel
noncomputable def cell2351 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2351.certificate 1621 accepted2351
noncomputable def cells : List CertifiedMinorantCell := [cell2344, cell2345, cell2346, cell2347, cell2348, cell2349, cell2350, cell2351]
theorem chainAccepted : minorantChainCheck (4933/5000) (4937/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4933/5000) (4937/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0293
