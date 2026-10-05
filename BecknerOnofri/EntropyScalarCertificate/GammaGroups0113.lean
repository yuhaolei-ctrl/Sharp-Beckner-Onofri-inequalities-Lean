module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0141
public import BecknerOnofri.EntropyScalarCertificate.Bessel0142
public import BecknerOnofri.EntropyScalarCertificate.Bessel0559
public import BecknerOnofri.EntropyScalarCertificate.Bessel0560
public import BecknerOnofri.EntropyScalarCertificate.Brackets0056
public import BecknerOnofri.EntropyScalarCertificate.Brackets0057
public import BecknerOnofri.EntropyScalarCertificate.Logs0113
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0904
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (2094606992521448263483954020122375550603/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2094606992521448263483954020122375550603/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (4202033892264263274622091182064672433283/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4202033892264263274622091182064672433283/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (8391247877307159801589999222309423534489/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8391247877307159801589999222309423534489/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0904 BracketBatch0056.bracket0905 (8391247877307159801589999222309423534489/20000000000000000000000000000000000000000) (736498572981766049551621423654663887/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0904 BracketBatch0056.bracket0905
  (8391247877307159801589999222309423534489/20000000000000000000000000000000000000000) (736498572981766049551621423654663887/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0904
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0905
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (6565677956662911366597017471976050677/15625000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6565677956662911366597017471976050677/15625000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (4214872166938840400411390582845339737419/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4214872166938840400411390582845339737419/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (8416906059203103675033481764910012170699/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8416906059203103675033481764910012170699/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0905 BracketBatch0056.bracket0906 (8416906059203103675033481764910012170699/20000000000000000000000000000000000000000) (9305424988870696193345794617346198239/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0905 BracketBatch0056.bracket0906
  (8416906059203103675033481764910012170699/20000000000000000000000000000000000000000) (9305424988870696193345794617346198239/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0905
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0906
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (526859020867355050051423822855667467177/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (526859020867355050051423822855667467177/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2113864452465815912748558009230058893521/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2113864452465815912748558009230058893521/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (4221300535935236112954253300652728762229/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4221300535935236112954253300652728762229/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0906 BracketBatch0056.bracket0907 (4221300535935236112954253300652728762229/10000000000000000000000000000000000000000) (18810893160883929080019441276936249353/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0906 BracketBatch0056.bracket0907
  (4221300535935236112954253300652728762229/10000000000000000000000000000000000000000) (18810893160883929080019441276936249353/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0906
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0907
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (4227728904931631825497116018460117787039/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4227728904931631825497116018460117787039/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (530075525333141419200898546657581421223/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (530075525333141419200898546657581421223/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (8468333107596763179104304391720769156823/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8468333107596763179104304391720769156823/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0907 BracketBatch0056.bracket0908 (8468333107596763179104304391720769156823/20000000000000000000000000000000000000000) (2376575515792604894912643905210465381/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0907 BracketBatch0056.bracket0908
  (8468333107596763179104304391720769156823/20000000000000000000000000000000000000000) (2376575515792604894912643905210465381/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0907
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0908
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0141.rows BesselBatch0141.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (4240604202665131353607188373260651369781/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4240604202665131353607188373260651369781/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (170139926284960242629124385484117609537/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (170139926284960242629124385484117609537/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (4247051179894568709667649005181795804103/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4247051179894568709667649005181795804103/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0908 BracketBatch0056.bracket0909 (4247051179894568709667649005181795804103/10000000000000000000000000000000000000000) (19215993174567621112389332112447005931/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0908 BracketBatch0056.bracket0909
  (4247051179894568709667649005181795804103/10000000000000000000000000000000000000000) (19215993174567621112389332112447005931/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0908
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0909
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (2126749078562003032864054818551470119211/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2126749078562003032864054818551470119211/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (853282173171965231227278522878720417027/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (853282173171965231227278522878720417027/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0559.rows BesselBatch0559.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (8519909022983832221864502251496542323557/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8519909022983832221864502251496542323557/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0909 BracketBatch0056.bracket0910 (8519909022983832221864502251496542323557/20000000000000000000000000000000000000000) (4855267663589693751233271654799758527/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0909 BracketBatch0056.bracket0910
  (8519909022983832221864502251496542323557/20000000000000000000000000000000000000000) (4855267663589693751233271654799758527/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0909
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0910
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1066602716464956539034098153598400521283/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1066602716464956539034098153598400521283/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (1069835606748960440956294770946896413131/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1069835606748960440956294770946896413131/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (1068219161606958489995196462272648467207/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1068219161606958489995196462272648467207/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0910 BracketBatch0056.bracket0911 (1068219161606958489995196462272648467207/2500000000000000000000000000000000000000) (19627846963102633687876523193077406763/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0910 BracketBatch0056.bracket0911
  (1068219161606958489995196462272648467207/2500000000000000000000000000000000000000) (19627846963102633687876523193077406763/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0910
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0911
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (4279342426995841763825179083787585652521/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4279342426995841763825179083787585652521/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0142.rows BesselBatch0142.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2146146469615903680476595288185424727739/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2146146469615903680476595288185424727739/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0560.rows BesselBatch0560.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (8571635366227649124778369660158435107999/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8571635366227649124778369660158435107999/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0113.rows ScalarLogs0113.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0056.bracket0911 BracketBatch0057.bracket0912 (8571635366227649124778369660158435107999/20000000000000000000000000000000000000000) (19836332547038469372148394954103156399/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0056.bracket0911 BracketBatch0057.bracket0912
  (8571635366227649124778369660158435107999/20000000000000000000000000000000000000000) (19836332547038469372148394954103156399/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0911
