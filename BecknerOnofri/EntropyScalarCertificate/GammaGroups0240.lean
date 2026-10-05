module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0300
public import BecknerOnofri.EntropyScalarCertificate.Bessel0301
public import BecknerOnofri.EntropyScalarCertificate.Bessel0638
public import BecknerOnofri.EntropyScalarCertificate.Bessel0639
public import BecknerOnofri.EntropyScalarCertificate.Brackets0120
public import BecknerOnofri.EntropyScalarCertificate.Logs0240
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1920
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (16544541746128088471084959930984354541701/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16544541746128088471084959930984354541701/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (665778927422121334815699765531284584489/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (665778927422121334815699765531284584489/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (16594507465840560920738727034633234576963/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16594507465840560920738727034633234576963/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1920 BracketBatch0120.bracket1921 (16594507465840560920738727034633234576963/5000000000000000000000000000000000000000) (169803128542495121869230780179050879549/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1920 BracketBatch0120.bracket1921
  (16594507465840560920738727034633234576963/5000000000000000000000000000000000000000) (169803128542495121869230780179050879549/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1920
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1921
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (33288946371106066740784988276564229224447/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (33288946371106066740784988276564229224447/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (16745701474740674850099448917762668616833/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16745701474740674850099448917762668616833/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (66780349320587416440983886112089566458113/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (66780349320587416440983886112089566458113/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1921 BracketBatch0120.bracket1922 (66780349320587416440983886112089566458113/20000000000000000000000000000000000000000) (682764088851318103139753986262061886919/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1921 BracketBatch0120.bracket1922
  (66780349320587416440983886112089566458113/20000000000000000000000000000000000000000) (682764088851318103139753986262061886919/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1921
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1922
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (33491402949481349700198897835525337233663/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (33491402949481349700198897835525337233663/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (33696503205317360027126745691253448329383/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (33696503205317360027126745691253448329383/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (33593953077399354863662821763389392781523/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33593953077399354863662821763389392781523/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1922 BracketBatch0120.bracket1923 (33593953077399354863662821763389392781523/10000000000000000000000000000000000000000) (1372686798421529418132604212791169184413/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1922 BracketBatch0120.bracket1923
  (33593953077399354863662821763389392781523/10000000000000000000000000000000000000000) (1372686798421529418132604212791169184413/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1922
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1923
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1684825160265868001356337284562672416469/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1684825160265868001356337284562672416469/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (16952149205972335423590850848595557709317/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16952149205972335423590850848595557709317/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (33800400808631015437154223694222281874007/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33800400808631015437154223694222281874007/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1923 BracketBatch0120.bracket1924 (33800400808631015437154223694222281874007/10000000000000000000000000000000000000000) (1379901539549113344312082964996637988241/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1923 BracketBatch0120.bracket1924
  (33800400808631015437154223694222281874007/10000000000000000000000000000000000000000) (1379901539549113344312082964996637988241/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1923
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1924
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (33904298411944670847181701697191115418631/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (33904298411944670847181701697191115418631/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (34114841180647908196627456690215702508501/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34114841180647908196627456690215702508501/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (17004784898148144760952289596851704481783/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17004784898148144760952289596851704481783/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1924 BracketBatch0120.bracket1925 (17004784898148144760952289596851704481783/5000000000000000000000000000000000000000) (693586531013194300662393717497817890697/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1924 BracketBatch0120.bracket1925
  (17004784898148144760952289596851704481783/5000000000000000000000000000000000000000) (693586531013194300662393717497817890697/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1924
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1925
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (17057420590323954098313728345107851254249/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17057420590323954098313728345107851254249/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (8582046376226191374773459649273148135473/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8582046376226191374773459649273148135473/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (6844302668555267369572129528730829505039/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6844302668555267369572129528730829505039/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1925 BracketBatch0120.bracket1926 (6844302668555267369572129528730829505039/2000000000000000000000000000000000000000) (1394502038992796943440028144112620683631/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1925 BracketBatch0120.bracket1926
  (6844302668555267369572129528730829505039/2000000000000000000000000000000000000000) (1394502038992796943440028144112620683631/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1925
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1926
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (34328185504904765499093838597092592541889/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (34328185504904765499093838597092592541889/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (17272193403191360509252250846709235602323/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17272193403191360509252250846709235602323/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (13774514462257497303519668058102212749307/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13774514462257497303519668058102212749307/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1926 BracketBatch0120.bracket1927 (13774514462257497303519668058102212749307/4000000000000000000000000000000000000000) (87618072256583569963439971904710146891/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1926 BracketBatch0120.bracket1927
  (13774514462257497303519668058102212749307/4000000000000000000000000000000000000000) (87618072256583569963439971904710146891/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1926
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1927
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (34544386806382721018504501693418471204643/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (34544386806382721018504501693418471204643/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0301.rows BesselBatch0301.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (34763501982775090362052567424020801372141/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34763501982775090362052567424020801372141/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0639.rows BesselBatch0639.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (4331743049322363211284816819839954536049/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4331743049322363211284816819839954536049/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0240.rows ScalarLogs0240.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0120.bracket1927 BracketBatch0120.bracket1928 (4331743049322363211284816819839954536049/1250000000000000000000000000000000000000) (1409335111867176721336139761228594436583/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0120.bracket1927 BracketBatch0120.bracket1928
  (4331743049322363211284816819839954536049/1250000000000000000000000000000000000000) (1409335111867176721336139761228594436583/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1927
