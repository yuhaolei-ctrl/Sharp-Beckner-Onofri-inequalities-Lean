import BecknerOnofri.EntropyScalarCertificate.Bessel0201
import BecknerOnofri.EntropyScalarCertificate.Bessel0202
import BecknerOnofri.EntropyScalarCertificate.Bessel0589
import BecknerOnofri.EntropyScalarCertificate.Bessel0590
import BecknerOnofri.EntropyScalarCertificate.Brackets0080
import BecknerOnofri.EntropyScalarCertificate.Brackets0081
import BecknerOnofri.EntropyScalarCertificate.Logs0161
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1288
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (3183580810803775624005178959184694200771/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3183580810803775624005178959184694200771/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (3195557734634146834480297345592100154687/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3195557734634146834480297345592100154687/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (3189569272718961229242738152388397177729/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3189569272718961229242738152388397177729/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1288 BracketBatch0080.bracket1289 (3189569272718961229242738152388397177729/2500000000000000000000000000000000000000) (396852999317930625268957515760109898889/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1288 BracketBatch0080.bracket1289
  (3189569272718961229242738152388397177729/2500000000000000000000000000000000000000) (396852999317930625268957515760109898889/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1288
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1289
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (2556446187707317467584237876473680123749/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2556446187707317467584237876473680123749/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (6415253991063848662238711310781464504503/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6415253991063848662238711310781464504503/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (25612738920664284662398612003931329627751/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25612738920664284662398612003931329627751/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1289 BracketBatch0080.bracket1290 (25612738920664284662398612003931329627751/20000000000000000000000000000000000000000) (199810423214749657821196112421400136377/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1289 BracketBatch0080.bracket1290
  (25612738920664284662398612003931329627751/20000000000000000000000000000000000000000) (199810423214749657821196112421400136377/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1289
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1290
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (12830507982127697324477422621562929009003/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12830507982127697324477422621562929009003/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1609894947257569353268816369412595770789/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1609894947257569353268816369412595770789/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (5141933512037650430125590715372739035063/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5141933512037650430125590715372739035063/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1290 BracketBatch0080.bracket1291 (5141933512037650430125590715372739035063/4000000000000000000000000000000000000000) (402409951437554980466549653771696069931/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1290 BracketBatch0080.bracket1291
  (5141933512037650430125590715372739035063/4000000000000000000000000000000000000000) (402409951437554980466549653771696069931/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1290
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1291
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (12879159578060554826150530955300766166309/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12879159578060554826150530955300766166309/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (12928191029355471718300369007187741484733/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12928191029355471718300369007187741484733/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (12903675303708013272225449981244253825521/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12903675303708013272225449981244253825521/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1291 BracketBatch0080.bracket1292 (12903675303708013272225449981244253825521/10000000000000000000000000000000000000000) (20261027312406501187687780803265736357/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1291 BracketBatch0080.bracket1292
  (12903675303708013272225449981244253825521/10000000000000000000000000000000000000000) (20261027312406501187687780803265736357/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1291
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1292
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0201.rows BesselBatch0201.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1292819102935547171830036900718774148473/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1292819102935547171830036900718774148473/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (3244401935075149815992084731262091830919/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3244401935075149815992084731262091830919/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (12952899384828035491134353966118054404203/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12952899384828035491134353966118054404203/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1292 BracketBatch0080.bracket1293 (12952899384828035491134353966118054404203/10000000000000000000000000000000000000000) (204026433244206866518094833113630786039/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1292 BracketBatch0080.bracket1293
  (12952899384828035491134353966118054404203/10000000000000000000000000000000000000000) (204026433244206866518094833113630786039/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1292
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1293
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (12977607740300599263968338925048367323673/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12977607740300599263968338925048367323673/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (6513707609417556585824282307185279838303/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6513707609417556585824282307185279838303/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0589.rows BesselBatch0589.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (26005022959135712435616903539418927000279/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26005022959135712435616903539418927000279/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1293 BracketBatch0080.bracket1294 (26005022959135712435616903539418927000279/20000000000000000000000000000000000000000) (410907151580335810975782087137762439063/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1293 BracketBatch0080.bracket1294
  (26005022959135712435616903539418927000279/20000000000000000000000000000000000000000) (410907151580335810975782087137762439063/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1293
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1294
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (13027415218835113171648564614370559676603/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13027415218835113171648564614370559676603/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (13077619078997900550203987973229521917649/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13077619078997900550203987973229521917649/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (6526258574458253430463138146900020398563/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6526258574458253430463138146900020398563/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1294 BracketBatch0080.bracket1295 (6526258574458253430463138146900020398563/5000000000000000000000000000000000000000) (413783644815719161020190067870824260381/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1294 BracketBatch0080.bracket1295
  (6526258574458253430463138146900020398563/5000000000000000000000000000000000000000) (413783644815719161020190067870824260381/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1294
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1295
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (6538809539498950275101993986614760958823/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6538809539498950275101993986614760958823/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0202.rows BesselBatch0202.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (13128225043443782898243296899496343407073/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13128225043443782898243296899496343407073/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0590.rows BesselBatch0590.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (26205844122441683448447284872725865324719/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26205844122441683448447284872725865324719/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0161.rows ScalarLogs0161.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0080.bracket1295 BracketBatch0081.bracket1296 (26205844122441683448447284872725865324719/20000000000000000000000000000000000000000) (83336518686606851410734181207649012203/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0080.bracket1295 BracketBatch0081.bracket1296
  (26205844122441683448447284872725865324719/20000000000000000000000000000000000000000) (83336518686606851410734181207649012203/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1295
