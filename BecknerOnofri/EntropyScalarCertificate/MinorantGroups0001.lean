import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0001
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0001
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0008 : minorantGammaCheck GammaPanel0008.certificate 0=true := by decide +kernel
noncomputable def cell0008 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0008.certificate 0 accepted0008
theorem accepted0009 : minorantGammaCheck GammaPanel0009.certificate 0=true := by decide +kernel
noncomputable def cell0009 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0009.certificate 0 accepted0009
theorem accepted0010 : minorantGammaCheck GammaPanel0010.certificate 0=true := by decide +kernel
noncomputable def cell0010 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0010.certificate 0 accepted0010
theorem accepted0011 : minorantGammaCheck GammaPanel0011.certificate 0=true := by decide +kernel
noncomputable def cell0011 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0011.certificate 0 accepted0011
theorem accepted0012 : minorantGammaCheck GammaPanel0012.certificate 0=true := by decide +kernel
noncomputable def cell0012 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0012.certificate 0 accepted0012
theorem accepted0013 : minorantGammaCheck GammaPanel0013.certificate 0=true := by decide +kernel
noncomputable def cell0013 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0013.certificate 0 accepted0013
theorem accepted0014 : minorantGammaCheck GammaPanel0014.certificate 0=true := by decide +kernel
noncomputable def cell0014 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0014.certificate 0 accepted0014
theorem accepted0015 : minorantGammaCheck GammaPanel0015.certificate 0=true := by decide +kernel
noncomputable def cell0015 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0015.certificate 0 accepted0015
noncomputable def cells : List CertifiedMinorantCell := [cell0008, cell0009, cell0010, cell0011, cell0012, cell0013, cell0014, cell0015]
theorem chainAccepted : minorantChainCheck (629/10000) (633/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (629/10000) (633/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0001
