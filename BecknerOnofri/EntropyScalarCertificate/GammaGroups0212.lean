import BecknerOnofri.EntropyScalarCertificate.Bessel0265
import BecknerOnofri.EntropyScalarCertificate.Bessel0266
import BecknerOnofri.EntropyScalarCertificate.Bessel0621
import BecknerOnofri.EntropyScalarCertificate.Bessel0622
import BecknerOnofri.EntropyScalarCertificate.Brackets0106
import BecknerOnofri.EntropyScalarCertificate.Logs0212
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1696
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (19778821704373569581844003844239331694091/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19778821704373569581844003844239331694091/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (4947877011167682070316566542070423640649/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4947877011167682070316566542070423640649/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (39570329749044297863110270012521026256687/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39570329749044297863110270012521026256687/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1696 BracketBatch0106.bracket1697 (39570329749044297863110270012521026256687/20000000000000000000000000000000000000000) (79010507656569604274507212574755973707/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1696 BracketBatch0106.bracket1697
  (39570329749044297863110270012521026256687/20000000000000000000000000000000000000000) (79010507656569604274507212574755973707/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1696
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1697
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (19791508044670728281266266168281694562593/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19791508044670728281266266168281694562593/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (19804213071031407392498272436354382638781/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19804213071031407392498272436354382638781/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (19797860557851067836882269302318038600687/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19797860557851067836882269302318038600687/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1697 BracketBatch0106.bracket1698 (19797860557851067836882269302318038600687/10000000000000000000000000000000000000000) (790757658489695576698415093411049244279/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1697 BracketBatch0106.bracket1698
  (19797860557851067836882269302318038600687/10000000000000000000000000000000000000000) (790757658489695576698415093411049244279/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1697
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1698
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (9902106535515703696249136218177191319389/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9902106535515703696249136218177191319389/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (3963387365203284884593103780866277195411/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3963387365203284884593103780866277195411/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (39621149897047831815463791340685768615833/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39621149897047831815463791340685768615833/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1698 BracketBatch0106.bracket1699 (39621149897047831815463791340685768615833/20000000000000000000000000000000000000000) (395705491546619918378088215792771229301/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1698 BracketBatch0106.bracket1699
  (39621149897047831815463791340685768615833/20000000000000000000000000000000000000000) (395705491546619918378088215792771229301/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1698
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1699
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (4954234206504106105741379726082846494263/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4954234206504106105741379726082846494263/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (9914839676154837072499216096133573646439/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9914839676154837072499216096133573646439/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (3964661617832609856796395109659853326993/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3964661617832609856796395109659853326993/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1699 BracketBatch0106.bracket1700 (3964661617832609856796395109659853326993/2000000000000000000000000000000000000000) (396032525788110058846375507585575957349/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1699 BracketBatch0106.bracket1700
  (3964661617832609856796395109659853326993/2000000000000000000000000000000000000000) (396032525788110058846375507585575957349/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1699
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1700
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (158637434818477393159987457538137178343/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (158637434818477393159987457538137178343/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (19842440692718558863999217896615291390213/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19842440692718558863999217896615291390213/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (2479507502814264563062353130555152417693/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2479507502814264563062353130555152417693/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1700 BracketBatch0106.bracket1701 (2479507502814264563062353130555152417693/1250000000000000000000000000000000000000) (792719865140840066762989368714175783507/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1700 BracketBatch0106.bracket1701
  (2479507502814264563062353130555152417693/1250000000000000000000000000000000000000) (792719865140840066762989368714175783507/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1700
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1701
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1984244069271855886399921789661529139021/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1984244069271855886399921789661529139021/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (79420883560697682003766819728450040111/40000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (79420883560697682003766819728450040111/40000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (992441539572324484123523070718195035449/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (992441539572324484123523070718195035449/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1701 BracketBatch0106.bracket1702 (992441539572324484123523070718195035449/500000000000000000000000000000000000000) (793375424991620682146468072113182390811/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1701 BracketBatch0106.bracket1702
  (992441539572324484123523070718195035449/500000000000000000000000000000000000000) (793375424991620682146468072113182390811/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1701
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1702
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (19855220890174420500941704932112510027747/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19855220890174420500941704932112510027747/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (9934009993866487249251413733829058963347/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9934009993866487249251413733829058963347/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (39723240877907394999444532399770627954441/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39723240877907394999444532399770627954441/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1702 BracketBatch0106.bracket1703 (39723240877907394999444532399770627954441/20000000000000000000000000000000000000000) (794031732335405327316616563889751548719/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1702 BracketBatch0106.bracket1703
  (39723240877907394999444532399770627954441/20000000000000000000000000000000000000000) (794031732335405327316616563889751548719/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1702
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1703
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (19868019987732974498502827467658117926691/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19868019987732974498502827467658117926691/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (19880838028574745560181162464494624792087/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19880838028574745560181162464494624792087/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (19874429008153860029341994966076371359389/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19874429008153860029341994966076371359389/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0212.rows ScalarLogs0212.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1703 BracketBatch0106.bracket1704 (19874429008153860029341994966076371359389/10000000000000000000000000000000000000000) (794688788381364761432092342690681933873/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1703 BracketBatch0106.bracket1704
  (19874429008153860029341994966076371359389/10000000000000000000000000000000000000000) (794688788381364761432092342690681933873/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1703
