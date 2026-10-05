module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0038

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0038
open CandidateBatch0038 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0608 : AffinePiece := pieces[568]'(by decide +kernel)
theorem intervalAccepted0608 : candidateIntervalCheck candidate0608 (1781/10000) (1783/10000) piece0608=true := by decide +kernel
noncomputable def cell0608 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0608 accepted0608 (1781/10000) (1783/10000) piece0608
    intervalAccepted0608 (fun t => piece_le_psi ⟨568,by decide +kernel⟩ t)
def piece0609 : AffinePiece := pieces[569]'(by decide +kernel)
theorem intervalAccepted0609 : candidateIntervalCheck candidate0609 (1783/10000) (357/2000) piece0609=true := by decide +kernel
noncomputable def cell0609 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0609 accepted0609 (1783/10000) (357/2000) piece0609
    intervalAccepted0609 (fun t => piece_le_psi ⟨569,by decide +kernel⟩ t)
def piece0610 : AffinePiece := pieces[570]'(by decide +kernel)
theorem intervalAccepted0610 : candidateIntervalCheck candidate0610 (357/2000) (1787/10000) piece0610=true := by decide +kernel
noncomputable def cell0610 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0610 accepted0610 (357/2000) (1787/10000) piece0610
    intervalAccepted0610 (fun t => piece_le_psi ⟨570,by decide +kernel⟩ t)
def piece0611 : AffinePiece := pieces[571]'(by decide +kernel)
theorem intervalAccepted0611 : candidateIntervalCheck candidate0611 (1787/10000) (1789/10000) piece0611=true := by decide +kernel
noncomputable def cell0611 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0611 accepted0611 (1787/10000) (1789/10000) piece0611
    intervalAccepted0611 (fun t => piece_le_psi ⟨571,by decide +kernel⟩ t)
def piece0612 : AffinePiece := pieces[572]'(by decide +kernel)
theorem intervalAccepted0612 : candidateIntervalCheck candidate0612 (1789/10000) (1791/10000) piece0612=true := by decide +kernel
noncomputable def cell0612 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0612 accepted0612 (1789/10000) (1791/10000) piece0612
    intervalAccepted0612 (fun t => piece_le_psi ⟨572,by decide +kernel⟩ t)
def piece0613 : AffinePiece := pieces[573]'(by decide +kernel)
theorem intervalAccepted0613 : candidateIntervalCheck candidate0613 (1791/10000) (1793/10000) piece0613=true := by decide +kernel
noncomputable def cell0613 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0613 accepted0613 (1791/10000) (1793/10000) piece0613
    intervalAccepted0613 (fun t => piece_le_psi ⟨573,by decide +kernel⟩ t)
def piece0614 : AffinePiece := pieces[574]'(by decide +kernel)
theorem intervalAccepted0614 : candidateIntervalCheck candidate0614 (1793/10000) (359/2000) piece0614=true := by decide +kernel
noncomputable def cell0614 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0614 accepted0614 (1793/10000) (359/2000) piece0614
    intervalAccepted0614 (fun t => piece_le_psi ⟨574,by decide +kernel⟩ t)
def piece0615 : AffinePiece := pieces[575]'(by decide +kernel)
theorem intervalAccepted0615 : candidateIntervalCheck candidate0615 (359/2000) (1797/10000) piece0615=true := by decide +kernel
noncomputable def cell0615 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0615 accepted0615 (359/2000) (1797/10000) piece0615
    intervalAccepted0615 (fun t => piece_le_psi ⟨575,by decide +kernel⟩ t)
def piece0616 : AffinePiece := pieces[576]'(by decide +kernel)
theorem intervalAccepted0616 : candidateIntervalCheck candidate0616 (1797/10000) (1799/10000) piece0616=true := by decide +kernel
noncomputable def cell0616 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0616 accepted0616 (1797/10000) (1799/10000) piece0616
    intervalAccepted0616 (fun t => piece_le_psi ⟨576,by decide +kernel⟩ t)
def piece0617 : AffinePiece := pieces[577]'(by decide +kernel)
theorem intervalAccepted0617 : candidateIntervalCheck candidate0617 (1799/10000) (1801/10000) piece0617=true := by decide +kernel
noncomputable def cell0617 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0617 accepted0617 (1799/10000) (1801/10000) piece0617
    intervalAccepted0617 (fun t => piece_le_psi ⟨577,by decide +kernel⟩ t)
def piece0618 : AffinePiece := pieces[578]'(by decide +kernel)
theorem intervalAccepted0618 : candidateIntervalCheck candidate0618 (1801/10000) (1803/10000) piece0618=true := by decide +kernel
noncomputable def cell0618 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0618 accepted0618 (1801/10000) (1803/10000) piece0618
    intervalAccepted0618 (fun t => piece_le_psi ⟨578,by decide +kernel⟩ t)
def piece0619 : AffinePiece := pieces[579]'(by decide +kernel)
theorem intervalAccepted0619 : candidateIntervalCheck candidate0619 (1803/10000) (361/2000) piece0619=true := by decide +kernel
noncomputable def cell0619 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0619 accepted0619 (1803/10000) (361/2000) piece0619
    intervalAccepted0619 (fun t => piece_le_psi ⟨579,by decide +kernel⟩ t)
def piece0620 : AffinePiece := pieces[580]'(by decide +kernel)
theorem intervalAccepted0620 : candidateIntervalCheck candidate0620 (361/2000) (1807/10000) piece0620=true := by decide +kernel
noncomputable def cell0620 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0620 accepted0620 (361/2000) (1807/10000) piece0620
    intervalAccepted0620 (fun t => piece_le_psi ⟨580,by decide +kernel⟩ t)
def piece0621 : AffinePiece := pieces[581]'(by decide +kernel)
theorem intervalAccepted0621 : candidateIntervalCheck candidate0621 (1807/10000) (1809/10000) piece0621=true := by decide +kernel
noncomputable def cell0621 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0621 accepted0621 (1807/10000) (1809/10000) piece0621
    intervalAccepted0621 (fun t => piece_le_psi ⟨581,by decide +kernel⟩ t)
def piece0622 : AffinePiece := pieces[582]'(by decide +kernel)
theorem intervalAccepted0622 : candidateIntervalCheck candidate0622 (1809/10000) (1811/10000) piece0622=true := by decide +kernel
noncomputable def cell0622 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0622 accepted0622 (1809/10000) (1811/10000) piece0622
    intervalAccepted0622 (fun t => piece_le_psi ⟨582,by decide +kernel⟩ t)
def piece0623 : AffinePiece := pieces[583]'(by decide +kernel)
theorem intervalAccepted0623 : candidateIntervalCheck candidate0623 (1811/10000) (1813/10000) piece0623=true := by decide +kernel
noncomputable def cell0623 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0623 accepted0623 (1811/10000) (1813/10000) piece0623
    intervalAccepted0623 (fun t => piece_le_psi ⟨583,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0608, cell0609, cell0610, cell0611, cell0612, cell0613, cell0614, cell0615, cell0616, cell0617, cell0618, cell0619, cell0620, cell0621, cell0622, cell0623]
theorem chainAccepted : spinCellChainCheck (1781/10000) (1813/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1781/10000) (1813/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0038
