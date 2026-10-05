import BecknerOnofri.EntropyScalarCertificate.Bessel0035
import BecknerOnofri.EntropyScalarCertificate.Bessel0036
import BecknerOnofri.EntropyScalarCertificate.Bessel0506
import BecknerOnofri.EntropyScalarCertificate.Bessel0507
import BecknerOnofri.EntropyScalarCertificate.Brackets0014
import BecknerOnofri.EntropyScalarCertificate.Logs0028
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0224
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (509121215061231888092154898806586871567/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (509121215061231888092154898806586871567/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1020273722612666625247392502231760130467/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1020273722612666625247392502231760130467/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (2038516152735130401431702299844933873601/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2038516152735130401431702299844933873601/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0224 BracketBatch0014.bracket0225 (2038516152735130401431702299844933873601/20000000000000000000000000000000000000000) (81963134254448799048682521211576079/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0224 BracketBatch0014.bracket0225
  (2038516152735130401431702299844933873601/20000000000000000000000000000000000000000) (81963134254448799048682521211576079/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0224
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0225
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (31883553831645832038981015694742504077/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31883553831645832038981015694742504077/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (511152570230700637435318127128157893399/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (511152570230700637435318127128157893399/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (1021289431537033950059014378244037958631/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1021289431537033950059014378244037958631/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0225 BracketBatch0014.bracket0226 (1021289431537033950059014378244037958631/10000000000000000000000000000000000000000) (8261693353900594151542767051124699/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0225 BracketBatch0014.bracket0226
  (1021289431537033950059014378244037958631/10000000000000000000000000000000000000000) (8261693353900594151542767051124699/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0225
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0226
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (204461028092280254974127250851263157359/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (204461028092280254974127250851263157359/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (256084170982509863355115324518627782941/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (256084170982509863355115324518627782941/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (2046641824391440728291097552330826918559/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2046641824391440728291097552330826918559/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0226 BracketBatch0014.bracket0227 (2046641824391440728291097552330826918559/20000000000000000000000000000000000000000) (41637312781740475533749181790085379/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0226 BracketBatch0014.bracket0227
  (2046641824391440728291097552330826918559/20000000000000000000000000000000000000000) (41637312781740475533749181790085379/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0226
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0227
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1024336683930039453420461298074511131761/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1024336683930039453420461298074511131761/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (513184176640020030159135872858721449709/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (513184176640020030159135872858721449709/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (2050705037210079513738733043791954031179/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2050705037210079513738733043791954031179/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0227 BracketBatch0014.bracket0228 (2050705037210079513738733043791954031179/20000000000000000000000000000000000000000) (16787245169080316412585872692287199/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0227 BracketBatch0014.bracket0228
  (2050705037210079513738733043791954031179/20000000000000000000000000000000000000000) (16787245169080316412585872692287199/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0227
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0228
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (205273670656008012063654349143488579883/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (205273670656008012063654349143488579883/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1028400148772949361267430008706713645563/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1028400148772949361267430008706713645563/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (1027384251026494710792850877212078272489/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1027384251026494710792850877212078272489/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0228 BracketBatch0014.bracket0229 (1027384251026494710792850877212078272489/10000000000000000000000000000000000000000) (84601749934124228387129798418441303/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0228 BracketBatch0014.bracket0229
  (1027384251026494710792850877212078272489/10000000000000000000000000000000000000000) (84601749934124228387129798418441303/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0228
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0229
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (25710003719323734031685750217667841139/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25710003719323734031685750217667841139/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (128804008833800147953450429867476703597/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (128804008833800147953450429867476703597/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (64338506857604704527969795238953977323/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64338506857604704527969795238953977323/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0229 BracketBatch0014.bracket0230 (64338506857604704527969795238953977323/625000000000000000000000000000000000000) (85271213410841654510000943753762843/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0229 BracketBatch0014.bracket0230
  (64338506857604704527969795238953977323/625000000000000000000000000000000000000) (85271213410841654510000943753762843/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0229
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0230
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0035.rows BesselBatch0035.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1030432070670401183627603438939813628773/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1030432070670401183627603438939813628773/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (129058014904264638992105563826234922901/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (129058014904264638992105563826234922901/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (2062896189904518295564447949549693011981/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2062896189904518295564447949549693011981/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0230 BracketBatch0014.bracket0231 (2062896189904518295564447949549693011981/20000000000000000000000000000000000000000) (85944631888590743453269741312159493/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0230 BracketBatch0014.bracket0231
  (2062896189904518295564447949549693011981/20000000000000000000000000000000000000000) (85944631888590743453269741312159493/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0230
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0231
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (206492823846823422387368902121975876641/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (206492823846823422387368902121975876641/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0036.rows BesselBatch0036.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (258624073681476670895441583202832693569/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (258624073681476670895441583202832693569/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0506.rows BesselBatch0506.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (2066960413960023795518610843421210157481/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2066960413960023795518610843421210157481/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0028.rows ScalarLogs0028.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0014.bracket0231 BracketBatch0014.bracket0232 (2066960413960023795518610843421210157481/20000000000000000000000000000000000000000) (86622021012260261678686923782398667/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0014.bracket0231 BracketBatch0014.bracket0232
  (2066960413960023795518610843421210157481/20000000000000000000000000000000000000000) (86622021012260261678686923782398667/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0231
