module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0118

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0118
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0944 : minorantGammaCheck GammaPanel0944.certificate 842=true := by decide +kernel
noncomputable def cell0944 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0944.certificate 842 accepted0944
theorem accepted0945 : minorantGammaCheck GammaPanel0945.certificate 843=true := by decide +kernel
noncomputable def cell0945 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0945.certificate 843 accepted0945
theorem accepted0946 : minorantGammaCheck GammaPanel0946.certificate 844=true := by decide +kernel
noncomputable def cell0946 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0946.certificate 844 accepted0946
theorem accepted0947 : minorantGammaCheck GammaPanel0947.certificate 845=true := by decide +kernel
noncomputable def cell0947 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0947.certificate 845 accepted0947
theorem accepted0948 : minorantGammaCheck GammaPanel0948.certificate 846=true := by decide +kernel
noncomputable def cell0948 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0948.certificate 846 accepted0948
theorem accepted0949 : minorantGammaCheck GammaPanel0949.certificate 847=true := by decide +kernel
noncomputable def cell0949 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0949.certificate 847 accepted0949
theorem accepted0950 : minorantGammaCheck GammaPanel0950.certificate 848=true := by decide +kernel
noncomputable def cell0950 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0950.certificate 848 accepted0950
theorem accepted0951 : minorantGammaCheck GammaPanel0951.certificate 849=true := by decide +kernel
noncomputable def cell0951 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0951.certificate 849 accepted0951
noncomputable def cells : List CertifiedMinorantCell := [cell0944, cell0945, cell0946, cell0947, cell0948, cell0949, cell0950, cell0951]
theorem chainAccepted : minorantChainCheck (213/500) (217/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (213/500) (217/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0118
