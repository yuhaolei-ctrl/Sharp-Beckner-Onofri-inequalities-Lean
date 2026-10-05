module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0103

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0103
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0824 : minorantGammaCheck GammaPanel0824.certificate 722=true := by decide +kernel
noncomputable def cell0824 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0824.certificate 722 accepted0824
theorem accepted0825 : minorantGammaCheck GammaPanel0825.certificate 723=true := by decide +kernel
noncomputable def cell0825 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0825.certificate 723 accepted0825
theorem accepted0826 : minorantGammaCheck GammaPanel0826.certificate 724=true := by decide +kernel
noncomputable def cell0826 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0826.certificate 724 accepted0826
theorem accepted0827 : minorantGammaCheck GammaPanel0827.certificate 725=true := by decide +kernel
noncomputable def cell0827 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0827.certificate 725 accepted0827
theorem accepted0828 : minorantGammaCheck GammaPanel0828.certificate 726=true := by decide +kernel
noncomputable def cell0828 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0828.certificate 726 accepted0828
theorem accepted0829 : minorantGammaCheck GammaPanel0829.certificate 727=true := by decide +kernel
noncomputable def cell0829 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0829.certificate 727 accepted0829
theorem accepted0830 : minorantGammaCheck GammaPanel0830.certificate 728=true := by decide +kernel
noncomputable def cell0830 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0830.certificate 728 accepted0830
theorem accepted0831 : minorantGammaCheck GammaPanel0831.certificate 729=true := by decide +kernel
noncomputable def cell0831 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0831.certificate 729 accepted0831
noncomputable def cells : List CertifiedMinorantCell := [cell0824, cell0825, cell0826, cell0827, cell0828, cell0829, cell0830, cell0831]
theorem chainAccepted : minorantChainCheck (153/500) (157/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (153/500) (157/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0103
