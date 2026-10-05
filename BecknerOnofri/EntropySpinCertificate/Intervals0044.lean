import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0044
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0044
open CandidateBatch0044 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0704 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0704 : candidateIntervalCheck candidate0704 (1973/10000) (79/400) piece0704=true := by decide +kernel
noncomputable def cell0704 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0704 accepted0704 (1973/10000) (79/400) piece0704
    intervalAccepted0704 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0705 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0705 : candidateIntervalCheck candidate0705 (79/400) (1977/10000) piece0705=true := by decide +kernel
noncomputable def cell0705 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0705 accepted0705 (79/400) (1977/10000) piece0705
    intervalAccepted0705 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0706 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0706 : candidateIntervalCheck candidate0706 (1977/10000) (1979/10000) piece0706=true := by decide +kernel
noncomputable def cell0706 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0706 accepted0706 (1977/10000) (1979/10000) piece0706
    intervalAccepted0706 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0707 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0707 : candidateIntervalCheck candidate0707 (1979/10000) (1981/10000) piece0707=true := by decide +kernel
noncomputable def cell0707 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0707 accepted0707 (1979/10000) (1981/10000) piece0707
    intervalAccepted0707 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0708 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0708 : candidateIntervalCheck candidate0708 (1981/10000) (1983/10000) piece0708=true := by decide +kernel
noncomputable def cell0708 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0708 accepted0708 (1981/10000) (1983/10000) piece0708
    intervalAccepted0708 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0709 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0709 : candidateIntervalCheck candidate0709 (1983/10000) (397/2000) piece0709=true := by decide +kernel
noncomputable def cell0709 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0709 accepted0709 (1983/10000) (397/2000) piece0709
    intervalAccepted0709 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0710 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0710 : candidateIntervalCheck candidate0710 (397/2000) (1987/10000) piece0710=true := by decide +kernel
noncomputable def cell0710 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0710 accepted0710 (397/2000) (1987/10000) piece0710
    intervalAccepted0710 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0711 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0711 : candidateIntervalCheck candidate0711 (1987/10000) (1989/10000) piece0711=true := by decide +kernel
noncomputable def cell0711 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0711 accepted0711 (1987/10000) (1989/10000) piece0711
    intervalAccepted0711 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0712 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0712 : candidateIntervalCheck candidate0712 (1989/10000) (1991/10000) piece0712=true := by decide +kernel
noncomputable def cell0712 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0712 accepted0712 (1989/10000) (1991/10000) piece0712
    intervalAccepted0712 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0713 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0713 : candidateIntervalCheck candidate0713 (1991/10000) (1993/10000) piece0713=true := by decide +kernel
noncomputable def cell0713 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0713 accepted0713 (1991/10000) (1993/10000) piece0713
    intervalAccepted0713 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0714 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0714 : candidateIntervalCheck candidate0714 (1993/10000) (399/2000) piece0714=true := by decide +kernel
noncomputable def cell0714 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0714 accepted0714 (1993/10000) (399/2000) piece0714
    intervalAccepted0714 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0715 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0715 : candidateIntervalCheck candidate0715 (399/2000) (1997/10000) piece0715=true := by decide +kernel
noncomputable def cell0715 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0715 accepted0715 (399/2000) (1997/10000) piece0715
    intervalAccepted0715 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0716 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0716 : candidateIntervalCheck candidate0716 (1997/10000) (1999/10000) piece0716=true := by decide +kernel
noncomputable def cell0716 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0716 accepted0716 (1997/10000) (1999/10000) piece0716
    intervalAccepted0716 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0717 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0717 : candidateIntervalCheck candidate0717 (1999/10000) (1/5) piece0717=true := by decide +kernel
noncomputable def cell0717 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0717 accepted0717 (1999/10000) (1/5) piece0717
    intervalAccepted0717 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0718 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0718 : candidateIntervalCheck candidate0718 (1/5) (201/1000) piece0718=true := by decide +kernel
noncomputable def cell0718 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0718 accepted0718 (1/5) (201/1000) piece0718
    intervalAccepted0718 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0719 : AffinePiece := pieces[617]'(by decide +kernel)
theorem intervalAccepted0719 : candidateIntervalCheck candidate0719 (201/1000) (101/500) piece0719=true := by decide +kernel
noncomputable def cell0719 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0719 accepted0719 (201/1000) (101/500) piece0719
    intervalAccepted0719 (fun t => piece_le_psi ⟨617,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0704, cell0705, cell0706, cell0707, cell0708, cell0709, cell0710, cell0711, cell0712, cell0713, cell0714, cell0715, cell0716, cell0717, cell0718, cell0719]
theorem chainAccepted : spinCellChainCheck (1973/10000) (101/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1973/10000) (101/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0044
