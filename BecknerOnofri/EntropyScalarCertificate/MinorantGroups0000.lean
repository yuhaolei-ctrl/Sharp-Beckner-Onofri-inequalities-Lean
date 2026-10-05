import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0000
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0000
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0000 : minorantGammaCheck GammaPanel0000.certificate 0=true := by decide +kernel
noncomputable def cell0000 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0000.certificate 0 accepted0000
theorem accepted0001 : minorantGammaCheck GammaPanel0001.certificate 0=true := by decide +kernel
noncomputable def cell0001 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0001.certificate 0 accepted0001
theorem accepted0002 : minorantGammaCheck GammaPanel0002.certificate 0=true := by decide +kernel
noncomputable def cell0002 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0002.certificate 0 accepted0002
theorem accepted0003 : minorantGammaCheck GammaPanel0003.certificate 0=true := by decide +kernel
noncomputable def cell0003 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0003.certificate 0 accepted0003
theorem accepted0004 : minorantGammaCheck GammaPanel0004.certificate 0=true := by decide +kernel
noncomputable def cell0004 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0004.certificate 0 accepted0004
theorem accepted0005 : minorantGammaCheck GammaPanel0005.certificate 0=true := by decide +kernel
noncomputable def cell0005 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0005.certificate 0 accepted0005
theorem accepted0006 : minorantGammaCheck GammaPanel0006.certificate 0=true := by decide +kernel
noncomputable def cell0006 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0006.certificate 0 accepted0006
theorem accepted0007 : minorantGammaCheck GammaPanel0007.certificate 0=true := by decide +kernel
noncomputable def cell0007 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0007.certificate 0 accepted0007
noncomputable def cells : List CertifiedMinorantCell := [cell0000, cell0001, cell0002, cell0003, cell0004, cell0005, cell0006, cell0007]
theorem chainAccepted : minorantChainCheck (1/16) (629/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1/16) (629/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0000
