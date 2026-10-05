module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0243

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0243
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1944 : minorantGammaCheck GammaPanel1944.certificate 1588=true := by decide +kernel
noncomputable def cell1944 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1944.certificate 1588 accepted1944
theorem accepted1945 : minorantGammaCheck GammaPanel1945.certificate 1589=true := by decide +kernel
noncomputable def cell1945 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1945.certificate 1589 accepted1945
theorem accepted1946 : minorantGammaCheck GammaPanel1946.certificate 1590=true := by decide +kernel
noncomputable def cell1946 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1946.certificate 1590 accepted1946
theorem accepted1947 : minorantGammaCheck GammaPanel1947.certificate 1591=true := by decide +kernel
noncomputable def cell1947 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1947.certificate 1591 accepted1947
theorem accepted1948 : minorantGammaCheck GammaPanel1948.certificate 1592=true := by decide +kernel
noncomputable def cell1948 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1948.certificate 1592 accepted1948
theorem accepted1949 : minorantGammaCheck GammaPanel1949.certificate 1593=true := by decide +kernel
noncomputable def cell1949 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1949.certificate 1593 accepted1949
theorem accepted1950 : minorantGammaCheck GammaPanel1950.certificate 1594=true := by decide +kernel
noncomputable def cell1950 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1950.certificate 1594 accepted1950
theorem accepted1951 : minorantGammaCheck GammaPanel1951.certificate 1595=true := by decide +kernel
noncomputable def cell1951 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1951.certificate 1595 accepted1951
noncomputable def cells : List CertifiedMinorantCell := [cell1944, cell1945, cell1946, cell1947, cell1948, cell1949, cell1950, cell1951]
theorem chainAccepted : minorantChainCheck (933/1000) (937/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (933/1000) (937/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0243
