module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0103

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0103
open CandidateBatch0103 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1648 : AffinePiece := pieces[1406]'(by decide +kernel)
theorem intervalAccepted1648 : candidateIntervalCheck candidate1648 (857/1000) (8571/10000) piece1648=true := by decide +kernel
noncomputable def cell1648 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1648 accepted1648 (857/1000) (8571/10000) piece1648
    intervalAccepted1648 (fun t => piece_le_psi ⟨1406,by decide +kernel⟩ t)
def piece1649 : AffinePiece := pieces[1407]'(by decide +kernel)
theorem intervalAccepted1649 : candidateIntervalCheck candidate1649 (8571/10000) (2143/2500) piece1649=true := by decide +kernel
noncomputable def cell1649 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1649 accepted1649 (8571/10000) (2143/2500) piece1649
    intervalAccepted1649 (fun t => piece_le_psi ⟨1407,by decide +kernel⟩ t)
def piece1650 : AffinePiece := pieces[1408]'(by decide +kernel)
theorem intervalAccepted1650 : candidateIntervalCheck candidate1650 (2143/2500) (8573/10000) piece1650=true := by decide +kernel
noncomputable def cell1650 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1650 accepted1650 (2143/2500) (8573/10000) piece1650
    intervalAccepted1650 (fun t => piece_le_psi ⟨1408,by decide +kernel⟩ t)
def piece1651 : AffinePiece := pieces[1409]'(by decide +kernel)
theorem intervalAccepted1651 : candidateIntervalCheck candidate1651 (8573/10000) (4287/5000) piece1651=true := by decide +kernel
noncomputable def cell1651 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1651 accepted1651 (8573/10000) (4287/5000) piece1651
    intervalAccepted1651 (fun t => piece_le_psi ⟨1409,by decide +kernel⟩ t)
def piece1652 : AffinePiece := pieces[1410]'(by decide +kernel)
theorem intervalAccepted1652 : candidateIntervalCheck candidate1652 (4287/5000) (343/400) piece1652=true := by decide +kernel
noncomputable def cell1652 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1652 accepted1652 (4287/5000) (343/400) piece1652
    intervalAccepted1652 (fun t => piece_le_psi ⟨1410,by decide +kernel⟩ t)
def piece1653 : AffinePiece := pieces[1411]'(by decide +kernel)
theorem intervalAccepted1653 : candidateIntervalCheck candidate1653 (343/400) (536/625) piece1653=true := by decide +kernel
noncomputable def cell1653 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1653 accepted1653 (343/400) (536/625) piece1653
    intervalAccepted1653 (fun t => piece_le_psi ⟨1411,by decide +kernel⟩ t)
def piece1654 : AffinePiece := pieces[1412]'(by decide +kernel)
theorem intervalAccepted1654 : candidateIntervalCheck candidate1654 (536/625) (8577/10000) piece1654=true := by decide +kernel
noncomputable def cell1654 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1654 accepted1654 (536/625) (8577/10000) piece1654
    intervalAccepted1654 (fun t => piece_le_psi ⟨1412,by decide +kernel⟩ t)
def piece1655 : AffinePiece := pieces[1413]'(by decide +kernel)
theorem intervalAccepted1655 : candidateIntervalCheck candidate1655 (8577/10000) (4289/5000) piece1655=true := by decide +kernel
noncomputable def cell1655 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1655 accepted1655 (8577/10000) (4289/5000) piece1655
    intervalAccepted1655 (fun t => piece_le_psi ⟨1413,by decide +kernel⟩ t)
def piece1656 : AffinePiece := pieces[1414]'(by decide +kernel)
theorem intervalAccepted1656 : candidateIntervalCheck candidate1656 (4289/5000) (8579/10000) piece1656=true := by decide +kernel
noncomputable def cell1656 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1656 accepted1656 (4289/5000) (8579/10000) piece1656
    intervalAccepted1656 (fun t => piece_le_psi ⟨1414,by decide +kernel⟩ t)
def piece1657 : AffinePiece := pieces[1415]'(by decide +kernel)
theorem intervalAccepted1657 : candidateIntervalCheck candidate1657 (8579/10000) (429/500) piece1657=true := by decide +kernel
noncomputable def cell1657 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1657 accepted1657 (8579/10000) (429/500) piece1657
    intervalAccepted1657 (fun t => piece_le_psi ⟨1415,by decide +kernel⟩ t)
def piece1658 : AffinePiece := pieces[1416]'(by decide +kernel)
theorem intervalAccepted1658 : candidateIntervalCheck candidate1658 (429/500) (8581/10000) piece1658=true := by decide +kernel
noncomputable def cell1658 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1658 accepted1658 (429/500) (8581/10000) piece1658
    intervalAccepted1658 (fun t => piece_le_psi ⟨1416,by decide +kernel⟩ t)
def piece1659 : AffinePiece := pieces[1417]'(by decide +kernel)
theorem intervalAccepted1659 : candidateIntervalCheck candidate1659 (8581/10000) (4291/5000) piece1659=true := by decide +kernel
noncomputable def cell1659 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1659 accepted1659 (8581/10000) (4291/5000) piece1659
    intervalAccepted1659 (fun t => piece_le_psi ⟨1417,by decide +kernel⟩ t)
def piece1660 : AffinePiece := pieces[1418]'(by decide +kernel)
theorem intervalAccepted1660 : candidateIntervalCheck candidate1660 (4291/5000) (8583/10000) piece1660=true := by decide +kernel
noncomputable def cell1660 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1660 accepted1660 (4291/5000) (8583/10000) piece1660
    intervalAccepted1660 (fun t => piece_le_psi ⟨1418,by decide +kernel⟩ t)
def piece1661 : AffinePiece := pieces[1419]'(by decide +kernel)
theorem intervalAccepted1661 : candidateIntervalCheck candidate1661 (8583/10000) (1073/1250) piece1661=true := by decide +kernel
noncomputable def cell1661 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1661 accepted1661 (8583/10000) (1073/1250) piece1661
    intervalAccepted1661 (fun t => piece_le_psi ⟨1419,by decide +kernel⟩ t)
def piece1662 : AffinePiece := pieces[1420]'(by decide +kernel)
theorem intervalAccepted1662 : candidateIntervalCheck candidate1662 (1073/1250) (1717/2000) piece1662=true := by decide +kernel
noncomputable def cell1662 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1662 accepted1662 (1073/1250) (1717/2000) piece1662
    intervalAccepted1662 (fun t => piece_le_psi ⟨1420,by decide +kernel⟩ t)
def piece1663 : AffinePiece := pieces[1421]'(by decide +kernel)
theorem intervalAccepted1663 : candidateIntervalCheck candidate1663 (1717/2000) (4293/5000) piece1663=true := by decide +kernel
noncomputable def cell1663 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1663 accepted1663 (1717/2000) (4293/5000) piece1663
    intervalAccepted1663 (fun t => piece_le_psi ⟨1421,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1648, cell1649, cell1650, cell1651, cell1652, cell1653, cell1654, cell1655, cell1656, cell1657, cell1658, cell1659, cell1660, cell1661, cell1662, cell1663]
theorem chainAccepted : spinCellChainCheck (857/1000) (4293/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (857/1000) (4293/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0103
