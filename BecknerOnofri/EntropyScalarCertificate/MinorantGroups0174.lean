module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0174

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0174
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1392 : minorantGammaCheck GammaPanel1392.certificate 1249=true := by decide +kernel
noncomputable def cell1392 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1392.certificate 1249 accepted1392
theorem accepted1393 : minorantGammaCheck GammaPanel1393.certificate 1249=true := by decide +kernel
noncomputable def cell1393 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1393.certificate 1249 accepted1393
theorem accepted1394 : minorantGammaCheck GammaPanel1394.certificate 1249=true := by decide +kernel
noncomputable def cell1394 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1394.certificate 1249 accepted1394
theorem accepted1395 : minorantGammaCheck GammaPanel1395.certificate 1249=true := by decide +kernel
noncomputable def cell1395 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1395.certificate 1249 accepted1395
theorem accepted1396 : minorantGammaCheck GammaPanel1396.certificate 1249=true := by decide +kernel
noncomputable def cell1396 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1396.certificate 1249 accepted1396
theorem accepted1397 : minorantGammaCheck GammaPanel1397.certificate 1249=true := by decide +kernel
noncomputable def cell1397 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1397.certificate 1249 accepted1397
theorem accepted1398 : minorantGammaCheck GammaPanel1398.certificate 1249=true := by decide +kernel
noncomputable def cell1398 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1398.certificate 1249 accepted1398
theorem accepted1399 : minorantGammaCheck GammaPanel1399.certificate 1249=true := by decide +kernel
noncomputable def cell1399 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1399.certificate 1249 accepted1399
noncomputable def cells : List CertifiedMinorantCell := [cell1392, cell1393, cell1394, cell1395, cell1396, cell1397, cell1398, cell1399]
theorem chainAccepted : minorantChainCheck (4157/5000) (4161/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4157/5000) (4161/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0174
