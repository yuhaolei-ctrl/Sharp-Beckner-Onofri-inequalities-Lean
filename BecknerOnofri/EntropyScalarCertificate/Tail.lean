module

public import BecknerOnofri.ScalarTailPoint
public import BecknerOnofri.ScalarMinorantBounds
public import BecknerOnofri.CircleSmallGamma
public import BecknerOnofri.EntropyScalarCertificate.Brackets0195
public import BecknerOnofri.EntropyScalarCertificate.Bessel0488

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.CertifiedMinorant
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def tailLogs : List LogRow := [
  ⟨(3216642702717847145202598572684754556500783147515438702066540768359069547709100193642890951463999304857240373277291733961901902967974990445668752130091079851749753535367171443048668496287791934533363401180757004738999166344412643933695255380122252547518393198109544403082804487094767917937175708329122529912958105883/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),3216642702717847145202598572684754556500783147515438702066540768359069547709100193642890951463999304857240373277291733961901902967974990445668752130091079851749753535367171443048668496287791934533363401180757004738999166344412643933695255380122252547518393198109544403082804487094767917937175708329122529912958105883,1723641332219371030852727564822160561127535346589097610280396686317562152320067443790206250607440183698057779234792478380202207559740228849869722344047208316913327692555368725935444380183534867995457372728780841287680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,(715),(496224133170442580548708897/1000000000000000000000000),(4962241331704425805487089/10000000000000000000000)⟩,
  ⟨(1999/1000),1999,1000,(0),(692647055518263011497959/1000000000000000000000000),(346323527759131505748981/500000000000000000000000)⟩,
  ⟨(1/1000),128,125,(-10),(-863469409872767131506747/125000000000000000000000),(-6907755278982137052053973/1000000000000000000000000)⟩
]
theorem tailLogsAccepted : tailLogs.all LogRow.check=true := by decide +kernel
def tailLogZ := checkedLogOfRows tailLogs tailLogsAccepted ⟨0,by decide⟩
def tailLogP := checkedLogOfRows tailLogs tailLogsAccepted ⟨1,by decide⟩
def tailLogM := checkedLogOfRows tailLogs tailLogsAccepted ⟨2,by decide⟩
def tailBessel := checkedBesselOfRows BesselBatch0488.rows BesselBatch0488.accepted ⟨53,by decide⟩
def tailBracket := BracketBatch0195.bracket3128
theorem tailPointAccepted : tailPointCheck tailBracket tailBessel tailLogZ tailLogP tailLogM (11/25)=true := by decide +kernel
theorem tailBase_point_lower : (11/25 : ℝ)≤tailBase (999/1000) := by
  have h := tailPoint_sound tailBracket tailBessel tailLogZ tailLogP tailLogM (11/25) tailPointAccepted
  have hm : tailBracket.mean=(999/1000 : ℚ) := by decide +kernel
  rw [hm] at h
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h
theorem psi_le_gamma_final {t : ℝ} (ht : (999/1000 : ℝ)≤t) (ht1 : t<1) : psi t≤gamma t := by
  have hpsi := psi_upper (show t∈Set.Icc (0 : ℝ) 1 from ⟨by linarith,ht1.le⟩)
  have hgamma := (tailBase_point_lower).trans (gamma_final_range_lower t ht ht1)
  linarith
theorem psi_le_gamma_small {t : ℝ} (ht : 0≤t) (ht1 : t≤1/16) : psi t≤gamma t := by
  rw [psi_small ht1]
  exact gamma_small_quartic_lower ht ht1
#print axioms tailBase_point_lower
#print axioms psi_le_gamma_final
end BecknerOnofri.HighDim.ScalarCertificate.CertifiedMinorant
