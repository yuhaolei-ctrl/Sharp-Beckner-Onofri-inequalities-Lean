import BecknerOnofri.ScalarCheckedBessel
import BecknerOnofri.EntropyScalarCertificate.Bessel0422
import BecknerOnofri.EntropyScalarCertificate.Bessel0423
import BecknerOnofri.EntropyScalarCertificate.Bessel0424
namespace BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0169
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def lo2704b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨32,by decide⟩
def lo2704b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨33,by decide⟩
def lo2704 : CheckedMoment :=
  CheckedMoment.ofBessel lo2704b1 lo2704b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2704b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨37,by decide⟩
def hi2704b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨38,by decide⟩
def hi2704 : CheckedMoment :=
  CheckedMoment.ofBessel hi2704b1 hi2704b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2704 : meanBracketCheck (24913/25000) lo2704 hi2704=true := by decide +kernel
def bracket2704 : MeanBracket := meanBracketOfMoments (24913/25000) lo2704 hi2704 accepted2704
def lo2705b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨42,by decide⟩
def lo2705b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨43,by decide⟩
def lo2705 : CheckedMoment :=
  CheckedMoment.ofBessel lo2705b1 lo2705b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2705b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨47,by decide⟩
def hi2705b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨48,by decide⟩
def hi2705 : CheckedMoment :=
  CheckedMoment.ofBessel hi2705b1 hi2705b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2705 : meanBracketCheck (49827/50000) lo2705 hi2705=true := by decide +kernel
def bracket2705 : MeanBracket := meanBracketOfMoments (49827/50000) lo2705 hi2705 accepted2705
def lo2706b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨52,by decide⟩
def lo2706b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨53,by decide⟩
def lo2706 : CheckedMoment :=
  CheckedMoment.ofBessel lo2706b1 lo2706b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2706b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨57,by decide⟩
def hi2706b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨58,by decide⟩
def hi2706 : CheckedMoment :=
  CheckedMoment.ofBessel hi2706b1 hi2706b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2706 : meanBracketCheck (12457/12500) lo2706 hi2706=true := by decide +kernel
def bracket2706 : MeanBracket := meanBracketOfMoments (12457/12500) lo2706 hi2706 accepted2706
def lo2707b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨62,by decide⟩
def lo2707b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0422.rows BesselBatch0422.accepted ⟨63,by decide⟩
def lo2707 : CheckedMoment :=
  CheckedMoment.ofBessel lo2707b1 lo2707b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2707b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨3,by decide⟩
def hi2707b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨4,by decide⟩
def hi2707 : CheckedMoment :=
  CheckedMoment.ofBessel hi2707b1 hi2707b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2707 : meanBracketCheck (49829/50000) lo2707 hi2707=true := by decide +kernel
def bracket2707 : MeanBracket := meanBracketOfMoments (49829/50000) lo2707 hi2707 accepted2707
def lo2708b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨8,by decide⟩
def lo2708b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨9,by decide⟩
def lo2708 : CheckedMoment :=
  CheckedMoment.ofBessel lo2708b1 lo2708b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2708b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨13,by decide⟩
def hi2708b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨14,by decide⟩
def hi2708 : CheckedMoment :=
  CheckedMoment.ofBessel hi2708b1 hi2708b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2708 : meanBracketCheck (4983/5000) lo2708 hi2708=true := by decide +kernel
def bracket2708 : MeanBracket := meanBracketOfMoments (4983/5000) lo2708 hi2708 accepted2708
def lo2709b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨18,by decide⟩
def lo2709b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨19,by decide⟩
def lo2709 : CheckedMoment :=
  CheckedMoment.ofBessel lo2709b1 lo2709b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2709b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨23,by decide⟩
def hi2709b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨24,by decide⟩
def hi2709 : CheckedMoment :=
  CheckedMoment.ofBessel hi2709b1 hi2709b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2709 : meanBracketCheck (49831/50000) lo2709 hi2709=true := by decide +kernel
def bracket2709 : MeanBracket := meanBracketOfMoments (49831/50000) lo2709 hi2709 accepted2709
def lo2710b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨28,by decide⟩
def lo2710b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨29,by decide⟩
def lo2710 : CheckedMoment :=
  CheckedMoment.ofBessel lo2710b1 lo2710b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2710b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨33,by decide⟩
def hi2710b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨34,by decide⟩
def hi2710 : CheckedMoment :=
  CheckedMoment.ofBessel hi2710b1 hi2710b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2710 : meanBracketCheck (6229/6250) lo2710 hi2710=true := by decide +kernel
def bracket2710 : MeanBracket := meanBracketOfMoments (6229/6250) lo2710 hi2710 accepted2710
def lo2711b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨38,by decide⟩
def lo2711b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨39,by decide⟩
def lo2711 : CheckedMoment :=
  CheckedMoment.ofBessel lo2711b1 lo2711b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2711b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨43,by decide⟩
def hi2711b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨44,by decide⟩
def hi2711 : CheckedMoment :=
  CheckedMoment.ofBessel hi2711b1 hi2711b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2711 : meanBracketCheck (49833/50000) lo2711 hi2711=true := by decide +kernel
def bracket2711 : MeanBracket := meanBracketOfMoments (49833/50000) lo2711 hi2711 accepted2711
def lo2712b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨48,by decide⟩
def lo2712b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨49,by decide⟩
def lo2712 : CheckedMoment :=
  CheckedMoment.ofBessel lo2712b1 lo2712b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2712b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨53,by decide⟩
def hi2712b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨54,by decide⟩
def hi2712 : CheckedMoment :=
  CheckedMoment.ofBessel hi2712b1 hi2712b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2712 : meanBracketCheck (24917/25000) lo2712 hi2712=true := by decide +kernel
def bracket2712 : MeanBracket := meanBracketOfMoments (24917/25000) lo2712 hi2712 accepted2712
def lo2713b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨58,by decide⟩
def lo2713b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨59,by decide⟩
def lo2713 : CheckedMoment :=
  CheckedMoment.ofBessel lo2713b1 lo2713b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2713b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0423.rows BesselBatch0423.accepted ⟨63,by decide⟩
def hi2713b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨0,by decide⟩
def hi2713 : CheckedMoment :=
  CheckedMoment.ofBessel hi2713b1 hi2713b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2713 : meanBracketCheck (9967/10000) lo2713 hi2713=true := by decide +kernel
def bracket2713 : MeanBracket := meanBracketOfMoments (9967/10000) lo2713 hi2713 accepted2713
def lo2714b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨4,by decide⟩
def lo2714b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨5,by decide⟩
def lo2714 : CheckedMoment :=
  CheckedMoment.ofBessel lo2714b1 lo2714b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2714b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨9,by decide⟩
def hi2714b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨10,by decide⟩
def hi2714 : CheckedMoment :=
  CheckedMoment.ofBessel hi2714b1 hi2714b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2714 : meanBracketCheck (12459/12500) lo2714 hi2714=true := by decide +kernel
def bracket2714 : MeanBracket := meanBracketOfMoments (12459/12500) lo2714 hi2714 accepted2714
def lo2715b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨14,by decide⟩
def lo2715b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨15,by decide⟩
def lo2715 : CheckedMoment :=
  CheckedMoment.ofBessel lo2715b1 lo2715b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2715b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨19,by decide⟩
def hi2715b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨20,by decide⟩
def hi2715 : CheckedMoment :=
  CheckedMoment.ofBessel hi2715b1 hi2715b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2715 : meanBracketCheck (49837/50000) lo2715 hi2715=true := by decide +kernel
def bracket2715 : MeanBracket := meanBracketOfMoments (49837/50000) lo2715 hi2715 accepted2715
def lo2716b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨24,by decide⟩
def lo2716b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨25,by decide⟩
def lo2716 : CheckedMoment :=
  CheckedMoment.ofBessel lo2716b1 lo2716b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2716b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨29,by decide⟩
def hi2716b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨30,by decide⟩
def hi2716 : CheckedMoment :=
  CheckedMoment.ofBessel hi2716b1 hi2716b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2716 : meanBracketCheck (24919/25000) lo2716 hi2716=true := by decide +kernel
def bracket2716 : MeanBracket := meanBracketOfMoments (24919/25000) lo2716 hi2716 accepted2716
def lo2717b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨34,by decide⟩
def lo2717b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨35,by decide⟩
def lo2717 : CheckedMoment :=
  CheckedMoment.ofBessel lo2717b1 lo2717b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2717b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨39,by decide⟩
def hi2717b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨40,by decide⟩
def hi2717 : CheckedMoment :=
  CheckedMoment.ofBessel hi2717b1 hi2717b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2717 : meanBracketCheck (49839/50000) lo2717 hi2717=true := by decide +kernel
def bracket2717 : MeanBracket := meanBracketOfMoments (49839/50000) lo2717 hi2717 accepted2717
def lo2718b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨44,by decide⟩
def lo2718b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨45,by decide⟩
def lo2718 : CheckedMoment :=
  CheckedMoment.ofBessel lo2718b1 lo2718b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2718b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨49,by decide⟩
def hi2718b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨50,by decide⟩
def hi2718 : CheckedMoment :=
  CheckedMoment.ofBessel hi2718b1 hi2718b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2718 : meanBracketCheck (623/625) lo2718 hi2718=true := by decide +kernel
def bracket2718 : MeanBracket := meanBracketOfMoments (623/625) lo2718 hi2718 accepted2718
def lo2719b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨54,by decide⟩
def lo2719b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨55,by decide⟩
def lo2719 : CheckedMoment :=
  CheckedMoment.ofBessel lo2719b1 lo2719b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def hi2719b0 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨59,by decide⟩
def hi2719b1 : CheckedBessel :=
  checkedBesselOfRows BesselBatch0424.rows BesselBatch0424.accepted ⟨60,by decide⟩
def hi2719 : CheckedMoment :=
  CheckedMoment.ofBessel hi2719b1 hi2719b0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem accepted2719 : meanBracketCheck (49841/50000) lo2719 hi2719=true := by decide +kernel
def bracket2719 : MeanBracket := meanBracketOfMoments (49841/50000) lo2719 hi2719 accepted2719
#print axioms bracket2704
end BecknerOnofri.HighDim.ScalarCertificate.BracketBatch0169
