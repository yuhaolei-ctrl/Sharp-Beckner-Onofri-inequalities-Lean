module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0023
public import BecknerOnofri.EntropyScalarCertificate.Bessel0024
public import BecknerOnofri.EntropyScalarCertificate.Bessel0025
public import BecknerOnofri.EntropyScalarCertificate.Bessel0500
public import BecknerOnofri.EntropyScalarCertificate.Bessel0501
public import BecknerOnofri.EntropyScalarCertificate.Brackets0009
public import BecknerOnofri.EntropyScalarCertificate.Brackets0010
public import BecknerOnofri.EntropyScalarCertificate.Logs0019
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0152
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (872301972267780640860419125159900018779/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (872301972267780640860419125159900018779/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (437162460206234984371708556735499419503/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (437162460206234984371708556735499419503/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (349325378536050121920767247726179771557/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (349325378536050121920767247726179771557/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0152 BracketBatch0009.bracket0153 (349325378536050121920767247726179771557/4000000000000000000000000000000000000000) (5519043165382269789767059965332211/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0152 BracketBatch0009.bracket0153
  (349325378536050121920767247726179771557/4000000000000000000000000000000000000000) (5519043165382269789767059965332211/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0152
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0153
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0023.rows BesselBatch0023.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (874324920412469968743417113470998839003/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (874324920412469968743417113470998839003/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (109543496914191168399380234277122273651/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (109543496914191168399380234277122273651/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1750672895725999315938458987687977028211/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1750672895725999315938458987687977028211/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0153 BracketBatch0009.bracket0154 (1750672895725999315938458987687977028211/20000000000000000000000000000000000000000) (8912918644699021166414953709904517/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0153 BracketBatch0009.bracket0154
  (1750672895725999315938458987687977028211/20000000000000000000000000000000000000000) (8912918644699021166414953709904517/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0153
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0154
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (175269595062705869439008374843395637841/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (175269595062705869439008374843395637841/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (109796392153319765358772079796928970573/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (109796392153319765358772079796928970573/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (1754719112540087470065218512592409953789/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1754719112540087470065218512592409953789/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0154 BracketBatch0009.bracket0155 (1754719112540087470065218512592409953789/20000000000000000000000000000000000000000) (449796997667211276976958769976833/100000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0154 BracketBatch0009.bracket0155
  (1754719112540087470065218512592409953789/20000000000000000000000000000000000000000) (449796997667211276976958769976833/100000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0154
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0155
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (878371137226558122870176638375431764581/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (878371137226558122870176638375431764581/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (440197203203614560770768224740033157311/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (440197203203614560770768224740033157311/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (1758765543633787244411713087855498079203/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1758765543633787244411713087855498079203/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0155 BracketBatch0009.bracket0156 (1758765543633787244411713087855498079203/20000000000000000000000000000000000000000) (22698839098917715529619754214992201/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0155 BracketBatch0009.bracket0156
  (1758765543633787244411713087855498079203/20000000000000000000000000000000000000000) (22698839098917715529619754214992201/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0155
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0156
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (880394406407229121541536449480066314619/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (880394406407229121541536449480066314619/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (882417783111288833637226568706623074469/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (882417783111288833637226568706623074469/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (55087880922453686099336344318334043409/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (55087880922453686099336344318334043409/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0156 BracketBatch0009.bracket0157 (55087880922453686099336344318334043409/625000000000000000000000000000000000000) (11454635448313251840470501916439401/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0156 BracketBatch0009.bracket0157
  (55087880922453686099336344318334043409/625000000000000000000000000000000000000) (11454635448313251840470501916439401/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0156
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0157
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (441208891555644416818613284353311537233/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (441208891555644416818613284353311537233/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (176888253518911519980156401435693288573/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (176888253518911519980156401435693288573/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (1766859050705846433538008575885089517331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1766859050705846433538008575885089517331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0157 BracketBatch0009.bracket0158 (1766859050705846433538008575885089517331/20000000000000000000000000000000000000000) (4624230386071117220473419117888059/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0157 BracketBatch0009.bracket0158
  (1766859050705846433538008575885089517331/20000000000000000000000000000000000000000) (4624230386071117220473419117888059/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0157
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0158
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (442220633797278799950391003589233221431/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (442220633797278799950391003589233221431/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (886464860112929797174019692173031212013/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (886464860112929797174019692173031212013/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (14167249021659899176598413594811981239/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14167249021659899176598413594811981239/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0158 BracketBatch0009.bracket0159 (14167249021659899176598413594811981239/160000000000000000000000000000000000000) (5833622217409515175488634780641383/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0158 BracketBatch0009.bracket0159
  (14167249021659899176598413594811981239/160000000000000000000000000000000000000) (5833622217409515175488634780641383/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0158
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0159
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0024.rows BesselBatch0024.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (88646486011292979717401969217303121201/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (88646486011292979717401969217303121201/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0025.rows BesselBatch0025.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (888488560922374024303035147646525451381/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (888488560922374024303035147646525451381/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0501.rows BesselBatch0501.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (1774953421035303821477054839819556663391/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1774953421035303821477054839819556663391/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0019.rows ScalarLogs0019.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0009.bracket0159 BracketBatch0010.bracket0160 (1774953421035303821477054839819556663391/20000000000000000000000000000000000000000) (47098576799349503274509835378856507/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0009.bracket0159 BracketBatch0010.bracket0160
  (1774953421035303821477054839819556663391/20000000000000000000000000000000000000000) (47098576799349503274509835378856507/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0159
