import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0275
import BecknerOnofri.EntropyScalarCertificate.Bessel0276
import BecknerOnofri.EntropyScalarCertificate.Bessel0277
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0110
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo1760b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨0,by decide⟩
def lo1760b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨1,by decide⟩
def lo1760 : CheckedMoment :=
  CheckedMoment.ofBessel lo1760b1 lo1760b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1760b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨5,by decide⟩
def hi1760b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨6,by decide⟩
def hi1760 : CheckedMoment :=
  CheckedMoment.ofBessel hi1760b1 hi1760b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1760 : meanBracketCheck (4341/5000) lo1760 hi1760=true := by decide +kernel
def bracket1760 : MeanBracket := meanBracketOfMoments (4341/5000) lo1760 hi1760 accepted1760
def lo1761b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨10,by decide⟩
def lo1761b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨11,by decide⟩
def lo1761 : CheckedMoment :=
  CheckedMoment.ofBessel lo1761b1 lo1761b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1761b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨15,by decide⟩
def hi1761b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨16,by decide⟩
def hi1761 : CheckedMoment :=
  CheckedMoment.ofBessel hi1761b1 hi1761b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1761 : meanBracketCheck (8683/10000) lo1761 hi1761=true := by decide +kernel
def bracket1761 : MeanBracket := meanBracketOfMoments (8683/10000) lo1761 hi1761 accepted1761
def lo1762b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨20,by decide⟩
def lo1762b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨21,by decide⟩
def lo1762 : CheckedMoment :=
  CheckedMoment.ofBessel lo1762b1 lo1762b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1762b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨25,by decide⟩
def hi1762b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨26,by decide⟩
def hi1762 : CheckedMoment :=
  CheckedMoment.ofBessel hi1762b1 hi1762b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1762 : meanBracketCheck (2171/2500) lo1762 hi1762=true := by decide +kernel
def bracket1762 : MeanBracket := meanBracketOfMoments (2171/2500) lo1762 hi1762 accepted1762
def lo1763b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨30,by decide⟩
def lo1763b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨31,by decide⟩
def lo1763 : CheckedMoment :=
  CheckedMoment.ofBessel lo1763b1 lo1763b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1763b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨35,by decide⟩
def hi1763b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨36,by decide⟩
def hi1763 : CheckedMoment :=
  CheckedMoment.ofBessel hi1763b1 hi1763b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1763 : meanBracketCheck (1737/2000) lo1763 hi1763=true := by decide +kernel
def bracket1763 : MeanBracket := meanBracketOfMoments (1737/2000) lo1763 hi1763 accepted1763
def lo1764b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨40,by decide⟩
def lo1764b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨41,by decide⟩
def lo1764 : CheckedMoment :=
  CheckedMoment.ofBessel lo1764b1 lo1764b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1764b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨45,by decide⟩
def hi1764b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨46,by decide⟩
def hi1764 : CheckedMoment :=
  CheckedMoment.ofBessel hi1764b1 hi1764b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1764 : meanBracketCheck (4343/5000) lo1764 hi1764=true := by decide +kernel
def bracket1764 : MeanBracket := meanBracketOfMoments (4343/5000) lo1764 hi1764 accepted1764
def lo1765b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨50,by decide⟩
def lo1765b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨51,by decide⟩
def lo1765 : CheckedMoment :=
  CheckedMoment.ofBessel lo1765b1 lo1765b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1765b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨55,by decide⟩
def hi1765b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨56,by decide⟩
def hi1765 : CheckedMoment :=
  CheckedMoment.ofBessel hi1765b1 hi1765b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1765 : meanBracketCheck (8687/10000) lo1765 hi1765=true := by decide +kernel
def bracket1765 : MeanBracket := meanBracketOfMoments (8687/10000) lo1765 hi1765 accepted1765
def lo1766b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨60,by decide⟩
def lo1766b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨61,by decide⟩
def lo1766 : CheckedMoment :=
  CheckedMoment.ofBessel lo1766b1 lo1766b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1766b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨1,by decide⟩
def hi1766b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨2,by decide⟩
def hi1766 : CheckedMoment :=
  CheckedMoment.ofBessel hi1766b1 hi1766b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1766 : meanBracketCheck (543/625) lo1766 hi1766=true := by decide +kernel
def bracket1766 : MeanBracket := meanBracketOfMoments (543/625) lo1766 hi1766 accepted1766
def lo1767b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨6,by decide⟩
def lo1767b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨7,by decide⟩
def lo1767 : CheckedMoment :=
  CheckedMoment.ofBessel lo1767b1 lo1767b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1767b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨11,by decide⟩
def hi1767b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨12,by decide⟩
def hi1767 : CheckedMoment :=
  CheckedMoment.ofBessel hi1767b1 hi1767b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1767 : meanBracketCheck (8689/10000) lo1767 hi1767=true := by decide +kernel
def bracket1767 : MeanBracket := meanBracketOfMoments (8689/10000) lo1767 hi1767 accepted1767
def lo1768b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨16,by decide⟩
def lo1768b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨17,by decide⟩
def lo1768 : CheckedMoment :=
  CheckedMoment.ofBessel lo1768b1 lo1768b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1768b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨21,by decide⟩
def hi1768b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨22,by decide⟩
def hi1768 : CheckedMoment :=
  CheckedMoment.ofBessel hi1768b1 hi1768b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1768 : meanBracketCheck (869/1000) lo1768 hi1768=true := by decide +kernel
def bracket1768 : MeanBracket := meanBracketOfMoments (869/1000) lo1768 hi1768 accepted1768
def lo1769b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨26,by decide⟩
def lo1769b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨27,by decide⟩
def lo1769 : CheckedMoment :=
  CheckedMoment.ofBessel lo1769b1 lo1769b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1769b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨31,by decide⟩
def hi1769b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨32,by decide⟩
def hi1769 : CheckedMoment :=
  CheckedMoment.ofBessel hi1769b1 hi1769b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1769 : meanBracketCheck (8691/10000) lo1769 hi1769=true := by decide +kernel
def bracket1769 : MeanBracket := meanBracketOfMoments (8691/10000) lo1769 hi1769 accepted1769
def lo1770b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨36,by decide⟩
def lo1770b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨37,by decide⟩
def lo1770 : CheckedMoment :=
  CheckedMoment.ofBessel lo1770b1 lo1770b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1770b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨41,by decide⟩
def hi1770b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨42,by decide⟩
def hi1770 : CheckedMoment :=
  CheckedMoment.ofBessel hi1770b1 hi1770b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1770 : meanBracketCheck (2173/2500) lo1770 hi1770=true := by decide +kernel
def bracket1770 : MeanBracket := meanBracketOfMoments (2173/2500) lo1770 hi1770 accepted1770
def lo1771b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨46,by decide⟩
def lo1771b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨47,by decide⟩
def lo1771 : CheckedMoment :=
  CheckedMoment.ofBessel lo1771b1 lo1771b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1771b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨51,by decide⟩
def hi1771b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨52,by decide⟩
def hi1771 : CheckedMoment :=
  CheckedMoment.ofBessel hi1771b1 hi1771b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1771 : meanBracketCheck (8693/10000) lo1771 hi1771=true := by decide +kernel
def bracket1771 : MeanBracket := meanBracketOfMoments (8693/10000) lo1771 hi1771 accepted1771
def lo1772b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨56,by decide⟩
def lo1772b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨57,by decide⟩
def lo1772 : CheckedMoment :=
  CheckedMoment.ofBessel lo1772b1 lo1772b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1772b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨61,by decide⟩
def hi1772b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨62,by decide⟩
def hi1772 : CheckedMoment :=
  CheckedMoment.ofBessel hi1772b1 hi1772b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1772 : meanBracketCheck (4347/5000) lo1772 hi1772=true := by decide +kernel
def bracket1772 : MeanBracket := meanBracketOfMoments (4347/5000) lo1772 hi1772 accepted1772
def lo1773b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨2,by decide⟩
def lo1773b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨3,by decide⟩
def lo1773 : CheckedMoment :=
  CheckedMoment.ofBessel lo1773b1 lo1773b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1773b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨7,by decide⟩
def hi1773b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨8,by decide⟩
def hi1773 : CheckedMoment :=
  CheckedMoment.ofBessel hi1773b1 hi1773b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1773 : meanBracketCheck (1739/2000) lo1773 hi1773=true := by decide +kernel
def bracket1773 : MeanBracket := meanBracketOfMoments (1739/2000) lo1773 hi1773 accepted1773
def lo1774b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨12,by decide⟩
def lo1774b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨13,by decide⟩
def lo1774 : CheckedMoment :=
  CheckedMoment.ofBessel lo1774b1 lo1774b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1774b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨17,by decide⟩
def hi1774b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨18,by decide⟩
def hi1774 : CheckedMoment :=
  CheckedMoment.ofBessel hi1774b1 hi1774b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1774 : meanBracketCheck (1087/1250) lo1774 hi1774=true := by decide +kernel
def bracket1774 : MeanBracket := meanBracketOfMoments (1087/1250) lo1774 hi1774 accepted1774
def lo1775b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨22,by decide⟩
def lo1775b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨23,by decide⟩
def lo1775 : CheckedMoment :=
  CheckedMoment.ofBessel lo1775b1 lo1775b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi1775b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨27,by decide⟩
def hi1775b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨28,by decide⟩
def hi1775 : CheckedMoment :=
  CheckedMoment.ofBessel hi1775b1 hi1775b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted1775 : meanBracketCheck (8697/10000) lo1775 hi1775=true := by decide +kernel
def bracket1775 : MeanBracket := meanBracketOfMoments (8697/10000) lo1775 hi1775 accepted1775
#print axioms bracket1760
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0110
