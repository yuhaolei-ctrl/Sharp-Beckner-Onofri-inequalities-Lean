import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0110
import BecknerOnofri.EntropyScalarCertificate.Bessel0111
import BecknerOnofri.EntropyScalarCertificate.Bessel0112
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0044
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo0704b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨0,by decide⟩
def lo0704b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨1,by decide⟩
def lo0704 : CheckedMoment :=
  CheckedMoment.ofBessel lo0704b1 lo0704b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0704b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨5,by decide⟩
def hi0704b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨6,by decide⟩
def hi0704 : CheckedMoment :=
  CheckedMoment.ofBessel hi0704b1 hi0704b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0704 : meanBracketCheck (1973/10000) lo0704 hi0704=true := by decide +kernel
def bracket0704 : MeanBracket := meanBracketOfMoments (1973/10000) lo0704 hi0704 accepted0704
def lo0705b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨10,by decide⟩
def lo0705b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨11,by decide⟩
def lo0705 : CheckedMoment :=
  CheckedMoment.ofBessel lo0705b1 lo0705b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0705b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨15,by decide⟩
def hi0705b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨16,by decide⟩
def hi0705 : CheckedMoment :=
  CheckedMoment.ofBessel hi0705b1 hi0705b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0705 : meanBracketCheck (79/400) lo0705 hi0705=true := by decide +kernel
def bracket0705 : MeanBracket := meanBracketOfMoments (79/400) lo0705 hi0705 accepted0705
def lo0706b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨20,by decide⟩
def lo0706b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨21,by decide⟩
def lo0706 : CheckedMoment :=
  CheckedMoment.ofBessel lo0706b1 lo0706b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0706b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨25,by decide⟩
def hi0706b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨26,by decide⟩
def hi0706 : CheckedMoment :=
  CheckedMoment.ofBessel hi0706b1 hi0706b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0706 : meanBracketCheck (1977/10000) lo0706 hi0706=true := by decide +kernel
def bracket0706 : MeanBracket := meanBracketOfMoments (1977/10000) lo0706 hi0706 accepted0706
def lo0707b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨30,by decide⟩
def lo0707b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨31,by decide⟩
def lo0707 : CheckedMoment :=
  CheckedMoment.ofBessel lo0707b1 lo0707b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0707b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨35,by decide⟩
def hi0707b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨36,by decide⟩
def hi0707 : CheckedMoment :=
  CheckedMoment.ofBessel hi0707b1 hi0707b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0707 : meanBracketCheck (1979/10000) lo0707 hi0707=true := by decide +kernel
def bracket0707 : MeanBracket := meanBracketOfMoments (1979/10000) lo0707 hi0707 accepted0707
def lo0708b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨40,by decide⟩
def lo0708b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨41,by decide⟩
def lo0708 : CheckedMoment :=
  CheckedMoment.ofBessel lo0708b1 lo0708b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0708b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨45,by decide⟩
def hi0708b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨46,by decide⟩
def hi0708 : CheckedMoment :=
  CheckedMoment.ofBessel hi0708b1 hi0708b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0708 : meanBracketCheck (1981/10000) lo0708 hi0708=true := by decide +kernel
def bracket0708 : MeanBracket := meanBracketOfMoments (1981/10000) lo0708 hi0708 accepted0708
def lo0709b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨50,by decide⟩
def lo0709b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨51,by decide⟩
def lo0709 : CheckedMoment :=
  CheckedMoment.ofBessel lo0709b1 lo0709b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0709b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨55,by decide⟩
def hi0709b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨56,by decide⟩
def hi0709 : CheckedMoment :=
  CheckedMoment.ofBessel hi0709b1 hi0709b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0709 : meanBracketCheck (1983/10000) lo0709 hi0709=true := by decide +kernel
def bracket0709 : MeanBracket := meanBracketOfMoments (1983/10000) lo0709 hi0709 accepted0709
def lo0710b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨60,by decide⟩
def lo0710b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0110.rows BesselBatch0110.accepted ⟨61,by decide⟩
def lo0710 : CheckedMoment :=
  CheckedMoment.ofBessel lo0710b1 lo0710b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0710b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨1,by decide⟩
def hi0710b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨2,by decide⟩
def hi0710 : CheckedMoment :=
  CheckedMoment.ofBessel hi0710b1 hi0710b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0710 : meanBracketCheck (397/2000) lo0710 hi0710=true := by decide +kernel
def bracket0710 : MeanBracket := meanBracketOfMoments (397/2000) lo0710 hi0710 accepted0710
def lo0711b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨6,by decide⟩
def lo0711b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨7,by decide⟩
def lo0711 : CheckedMoment :=
  CheckedMoment.ofBessel lo0711b1 lo0711b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0711b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨11,by decide⟩
def hi0711b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨12,by decide⟩
def hi0711 : CheckedMoment :=
  CheckedMoment.ofBessel hi0711b1 hi0711b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0711 : meanBracketCheck (1987/10000) lo0711 hi0711=true := by decide +kernel
def bracket0711 : MeanBracket := meanBracketOfMoments (1987/10000) lo0711 hi0711 accepted0711
def lo0712b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨16,by decide⟩
def lo0712b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨17,by decide⟩
def lo0712 : CheckedMoment :=
  CheckedMoment.ofBessel lo0712b1 lo0712b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0712b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨21,by decide⟩
def hi0712b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨22,by decide⟩
def hi0712 : CheckedMoment :=
  CheckedMoment.ofBessel hi0712b1 hi0712b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0712 : meanBracketCheck (1989/10000) lo0712 hi0712=true := by decide +kernel
def bracket0712 : MeanBracket := meanBracketOfMoments (1989/10000) lo0712 hi0712 accepted0712
def lo0713b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨26,by decide⟩
def lo0713b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨27,by decide⟩
def lo0713 : CheckedMoment :=
  CheckedMoment.ofBessel lo0713b1 lo0713b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0713b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨31,by decide⟩
def hi0713b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨32,by decide⟩
def hi0713 : CheckedMoment :=
  CheckedMoment.ofBessel hi0713b1 hi0713b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0713 : meanBracketCheck (1991/10000) lo0713 hi0713=true := by decide +kernel
def bracket0713 : MeanBracket := meanBracketOfMoments (1991/10000) lo0713 hi0713 accepted0713
def lo0714b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨36,by decide⟩
def lo0714b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨37,by decide⟩
def lo0714 : CheckedMoment :=
  CheckedMoment.ofBessel lo0714b1 lo0714b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0714b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨41,by decide⟩
def hi0714b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨42,by decide⟩
def hi0714 : CheckedMoment :=
  CheckedMoment.ofBessel hi0714b1 hi0714b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0714 : meanBracketCheck (1993/10000) lo0714 hi0714=true := by decide +kernel
def bracket0714 : MeanBracket := meanBracketOfMoments (1993/10000) lo0714 hi0714 accepted0714
def lo0715b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨46,by decide⟩
def lo0715b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨47,by decide⟩
def lo0715 : CheckedMoment :=
  CheckedMoment.ofBessel lo0715b1 lo0715b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0715b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨51,by decide⟩
def hi0715b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨52,by decide⟩
def hi0715 : CheckedMoment :=
  CheckedMoment.ofBessel hi0715b1 hi0715b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0715 : meanBracketCheck (399/2000) lo0715 hi0715=true := by decide +kernel
def bracket0715 : MeanBracket := meanBracketOfMoments (399/2000) lo0715 hi0715 accepted0715
def lo0716b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨56,by decide⟩
def lo0716b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨57,by decide⟩
def lo0716 : CheckedMoment :=
  CheckedMoment.ofBessel lo0716b1 lo0716b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0716b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨61,by decide⟩
def hi0716b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨62,by decide⟩
def hi0716 : CheckedMoment :=
  CheckedMoment.ofBessel hi0716b1 hi0716b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0716 : meanBracketCheck (1997/10000) lo0716 hi0716=true := by decide +kernel
def bracket0716 : MeanBracket := meanBracketOfMoments (1997/10000) lo0716 hi0716 accepted0716
def lo0717b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨2,by decide⟩
def lo0717b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨3,by decide⟩
def lo0717 : CheckedMoment :=
  CheckedMoment.ofBessel lo0717b1 lo0717b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0717b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨7,by decide⟩
def hi0717b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨8,by decide⟩
def hi0717 : CheckedMoment :=
  CheckedMoment.ofBessel hi0717b1 hi0717b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0717 : meanBracketCheck (1999/10000) lo0717 hi0717=true := by decide +kernel
def bracket0717 : MeanBracket := meanBracketOfMoments (1999/10000) lo0717 hi0717 accepted0717
def lo0718b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨12,by decide⟩
def lo0718b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨13,by decide⟩
def lo0718 : CheckedMoment :=
  CheckedMoment.ofBessel lo0718b1 lo0718b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0718b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨17,by decide⟩
def hi0718b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨18,by decide⟩
def hi0718 : CheckedMoment :=
  CheckedMoment.ofBessel hi0718b1 hi0718b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0718 : meanBracketCheck (1/5) lo0718 hi0718=true := by decide +kernel
def bracket0718 : MeanBracket := meanBracketOfMoments (1/5) lo0718 hi0718 accepted0718
def lo0719b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨22,by decide⟩
def lo0719b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨23,by decide⟩
def lo0719 : CheckedMoment :=
  CheckedMoment.ofBessel lo0719b1 lo0719b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi0719b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨27,by decide⟩
def hi0719b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨28,by decide⟩
def hi0719 : CheckedMoment :=
  CheckedMoment.ofBessel hi0719b1 hi0719b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted0719 : meanBracketCheck (201/1000) lo0719 hi0719=true := by decide +kernel
def bracket0719 : MeanBracket := meanBracketOfMoments (201/1000) lo0719 hi0719 accepted0719
#print axioms bracket0704
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0044
