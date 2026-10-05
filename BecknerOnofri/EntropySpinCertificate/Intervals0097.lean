module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0097

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0097
open CandidateBatch0097 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1552 : AffinePiece := pieces[1310]'(by decide +kernel)
theorem intervalAccepted1552 : candidateIntervalCheck candidate1552 (4237/5000) (339/400) piece1552=true := by decide +kernel
noncomputable def cell1552 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1552 accepted1552 (4237/5000) (339/400) piece1552
    intervalAccepted1552 (fun t => piece_le_psi ⟨1310,by decide +kernel⟩ t)
def piece1553 : AffinePiece := pieces[1311]'(by decide +kernel)
theorem intervalAccepted1553 : candidateIntervalCheck candidate1553 (339/400) (2119/2500) piece1553=true := by decide +kernel
noncomputable def cell1553 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1553 accepted1553 (339/400) (2119/2500) piece1553
    intervalAccepted1553 (fun t => piece_le_psi ⟨1311,by decide +kernel⟩ t)
def piece1554 : AffinePiece := pieces[1312]'(by decide +kernel)
theorem intervalAccepted1554 : candidateIntervalCheck candidate1554 (2119/2500) (8477/10000) piece1554=true := by decide +kernel
noncomputable def cell1554 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1554 accepted1554 (2119/2500) (8477/10000) piece1554
    intervalAccepted1554 (fun t => piece_le_psi ⟨1312,by decide +kernel⟩ t)
def piece1555 : AffinePiece := pieces[1313]'(by decide +kernel)
theorem intervalAccepted1555 : candidateIntervalCheck candidate1555 (8477/10000) (4239/5000) piece1555=true := by decide +kernel
noncomputable def cell1555 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1555 accepted1555 (8477/10000) (4239/5000) piece1555
    intervalAccepted1555 (fun t => piece_le_psi ⟨1313,by decide +kernel⟩ t)
def piece1556 : AffinePiece := pieces[1314]'(by decide +kernel)
theorem intervalAccepted1556 : candidateIntervalCheck candidate1556 (4239/5000) (8479/10000) piece1556=true := by decide +kernel
noncomputable def cell1556 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1556 accepted1556 (4239/5000) (8479/10000) piece1556
    intervalAccepted1556 (fun t => piece_le_psi ⟨1314,by decide +kernel⟩ t)
def piece1557 : AffinePiece := pieces[1315]'(by decide +kernel)
theorem intervalAccepted1557 : candidateIntervalCheck candidate1557 (8479/10000) (106/125) piece1557=true := by decide +kernel
noncomputable def cell1557 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1557 accepted1557 (8479/10000) (106/125) piece1557
    intervalAccepted1557 (fun t => piece_le_psi ⟨1315,by decide +kernel⟩ t)
def piece1558 : AffinePiece := pieces[1316]'(by decide +kernel)
theorem intervalAccepted1558 : candidateIntervalCheck candidate1558 (106/125) (8481/10000) piece1558=true := by decide +kernel
noncomputable def cell1558 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1558 accepted1558 (106/125) (8481/10000) piece1558
    intervalAccepted1558 (fun t => piece_le_psi ⟨1316,by decide +kernel⟩ t)
def piece1559 : AffinePiece := pieces[1317]'(by decide +kernel)
theorem intervalAccepted1559 : candidateIntervalCheck candidate1559 (8481/10000) (4241/5000) piece1559=true := by decide +kernel
noncomputable def cell1559 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1559 accepted1559 (8481/10000) (4241/5000) piece1559
    intervalAccepted1559 (fun t => piece_le_psi ⟨1317,by decide +kernel⟩ t)
def piece1560 : AffinePiece := pieces[1318]'(by decide +kernel)
theorem intervalAccepted1560 : candidateIntervalCheck candidate1560 (4241/5000) (8483/10000) piece1560=true := by decide +kernel
noncomputable def cell1560 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1560 accepted1560 (4241/5000) (8483/10000) piece1560
    intervalAccepted1560 (fun t => piece_le_psi ⟨1318,by decide +kernel⟩ t)
def piece1561 : AffinePiece := pieces[1319]'(by decide +kernel)
theorem intervalAccepted1561 : candidateIntervalCheck candidate1561 (8483/10000) (2121/2500) piece1561=true := by decide +kernel
noncomputable def cell1561 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1561 accepted1561 (8483/10000) (2121/2500) piece1561
    intervalAccepted1561 (fun t => piece_le_psi ⟨1319,by decide +kernel⟩ t)
def piece1562 : AffinePiece := pieces[1320]'(by decide +kernel)
theorem intervalAccepted1562 : candidateIntervalCheck candidate1562 (2121/2500) (1697/2000) piece1562=true := by decide +kernel
noncomputable def cell1562 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1562 accepted1562 (2121/2500) (1697/2000) piece1562
    intervalAccepted1562 (fun t => piece_le_psi ⟨1320,by decide +kernel⟩ t)
def piece1563 : AffinePiece := pieces[1321]'(by decide +kernel)
theorem intervalAccepted1563 : candidateIntervalCheck candidate1563 (1697/2000) (4243/5000) piece1563=true := by decide +kernel
noncomputable def cell1563 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1563 accepted1563 (1697/2000) (4243/5000) piece1563
    intervalAccepted1563 (fun t => piece_le_psi ⟨1321,by decide +kernel⟩ t)
def piece1564 : AffinePiece := pieces[1322]'(by decide +kernel)
theorem intervalAccepted1564 : candidateIntervalCheck candidate1564 (4243/5000) (8487/10000) piece1564=true := by decide +kernel
noncomputable def cell1564 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1564 accepted1564 (4243/5000) (8487/10000) piece1564
    intervalAccepted1564 (fun t => piece_le_psi ⟨1322,by decide +kernel⟩ t)
def piece1565 : AffinePiece := pieces[1323]'(by decide +kernel)
theorem intervalAccepted1565 : candidateIntervalCheck candidate1565 (8487/10000) (1061/1250) piece1565=true := by decide +kernel
noncomputable def cell1565 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1565 accepted1565 (8487/10000) (1061/1250) piece1565
    intervalAccepted1565 (fun t => piece_le_psi ⟨1323,by decide +kernel⟩ t)
def piece1566 : AffinePiece := pieces[1324]'(by decide +kernel)
theorem intervalAccepted1566 : candidateIntervalCheck candidate1566 (1061/1250) (8489/10000) piece1566=true := by decide +kernel
noncomputable def cell1566 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1566 accepted1566 (1061/1250) (8489/10000) piece1566
    intervalAccepted1566 (fun t => piece_le_psi ⟨1324,by decide +kernel⟩ t)
def piece1567 : AffinePiece := pieces[1325]'(by decide +kernel)
theorem intervalAccepted1567 : candidateIntervalCheck candidate1567 (8489/10000) (849/1000) piece1567=true := by decide +kernel
noncomputable def cell1567 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1567 accepted1567 (8489/10000) (849/1000) piece1567
    intervalAccepted1567 (fun t => piece_le_psi ⟨1325,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1552, cell1553, cell1554, cell1555, cell1556, cell1557, cell1558, cell1559, cell1560, cell1561, cell1562, cell1563, cell1564, cell1565, cell1566, cell1567]
theorem chainAccepted : spinCellChainCheck (4237/5000) (849/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4237/5000) (849/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0097
