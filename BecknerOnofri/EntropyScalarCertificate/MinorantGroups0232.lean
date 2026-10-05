module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0232

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0232
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1856 : minorantGammaCheck GammaPanel1856.certificate 1500=true := by decide +kernel
noncomputable def cell1856 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1856.certificate 1500 accepted1856
theorem accepted1857 : minorantGammaCheck GammaPanel1857.certificate 1501=true := by decide +kernel
noncomputable def cell1857 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1857.certificate 1501 accepted1857
theorem accepted1858 : minorantGammaCheck GammaPanel1858.certificate 1502=true := by decide +kernel
noncomputable def cell1858 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1858.certificate 1502 accepted1858
theorem accepted1859 : minorantGammaCheck GammaPanel1859.certificate 1503=true := by decide +kernel
noncomputable def cell1859 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1859.certificate 1503 accepted1859
theorem accepted1860 : minorantGammaCheck GammaPanel1860.certificate 1504=true := by decide +kernel
noncomputable def cell1860 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1860.certificate 1504 accepted1860
theorem accepted1861 : minorantGammaCheck GammaPanel1861.certificate 1505=true := by decide +kernel
noncomputable def cell1861 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1861.certificate 1505 accepted1861
theorem accepted1862 : minorantGammaCheck GammaPanel1862.certificate 1506=true := by decide +kernel
noncomputable def cell1862 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1862.certificate 1506 accepted1862
theorem accepted1863 : minorantGammaCheck GammaPanel1863.certificate 1507=true := by decide +kernel
noncomputable def cell1863 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1863.certificate 1507 accepted1863
noncomputable def cells : List CertifiedMinorantCell := [cell1856, cell1857, cell1858, cell1859, cell1860, cell1861, cell1862, cell1863]
theorem chainAccepted : minorantChainCheck (889/1000) (893/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (889/1000) (893/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0232
