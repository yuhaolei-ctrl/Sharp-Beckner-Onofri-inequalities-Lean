module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0021
public import BecknerOnofri.EntropyScalarCertificate.Bessel0022
public import BecknerOnofri.EntropyScalarCertificate.Bessel0499
public import BecknerOnofri.EntropyScalarCertificate.Bessel0500
public import BecknerOnofri.EntropyScalarCertificate.Brackets0008
public import BecknerOnofri.EntropyScalarCertificate.Brackets0009
public import BecknerOnofri.EntropyScalarCertificate.Logs0017
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0136
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (167989822506389295610560270577149512377/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (167989822506389295610560270577149512377/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (841970387276984444305788353671525411559/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (841970387276984444305788353671525411559/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (420479874952232730589647426639318243361/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (420479874952232730589647426639318243361/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0136 BracketBatch0008.bracket0137 (420479874952232730589647426639318243361/5000000000000000000000000000000000000000) (18967233775024877809319886275866829/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0136 BracketBatch0008.bracket0137
  (420479874952232730589647426639318243361/5000000000000000000000000000000000000000) (18967233775024877809319886275866829/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0136
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0137
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (210492596819246111076447088417881352889/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (210492596819246111076447088417881352889/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (843991764698645145644002226775566365523/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (843991764698645145644002226775566365523/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1685962151975629589949790580447091777079/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1685962151975629589949790580447091777079/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0137 BracketBatch0008.bracket0138 (1685962151975629589949790580447091777079/20000000000000000000000000000000000000000) (19151376493847814120828506318672879/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0137 BracketBatch0008.bracket0138
  (1685962151975629589949790580447091777079/20000000000000000000000000000000000000000) (19151376493847814120828506318672879/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0137
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0138
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (10549897058733064320550027834694579569/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10549897058733064320550027834694579569/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (846013245051377397279545161203793578009/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (846013245051377397279545161203793578009/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (1690005009750022542923547387979359943529/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1690005009750022542923547387979359943529/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0138 BracketBatch0008.bracket0139 (1690005009750022542923547387979359943529/20000000000000000000000000000000000000000) (4834211175048207707236755834778159/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0138 BracketBatch0008.bracket0139
  (1690005009750022542923547387979359943529/20000000000000000000000000000000000000000) (4834211175048207707236755834778159/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0138
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0139
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (423006622525688698639772580601896789003/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (423006622525688698639772580601896789003/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (848034828589700541329772227585793221897/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (848034828589700541329772227585793221897/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (1694048073641077938609317388789586799903/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1694048073641077938609317388789586799903/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0139 BracketBatch0008.bracket0140 (1694048073641077938609317388789586799903/20000000000000000000000000000000000000000) (2440455595815227335601064876545939/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0139 BracketBatch0008.bracket0140
  (1694048073641077938609317388789586799903/20000000000000000000000000000000000000000) (2440455595815227335601064876545939/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0139
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0140
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0021.rows BesselBatch0021.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (424017414294850270664886113792896610947/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (424017414294850270664886113792896610947/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (850056515568204630439935909485427525673/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (850056515568204630439935909485427525673/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1698091344157905171769708137071220747567/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1698091344157905171769708137071220747567/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0140 BracketBatch0008.bracket0141 (1698091344157905171769708137071220747567/20000000000000000000000000000000000000000) (39423566156931015931566398683601331/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0140 BracketBatch0008.bracket0141
  (1698091344157905171769708137071220747567/20000000000000000000000000000000000000000) (39423566156931015931566398683601331/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0140
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0141
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (85005651556820463043993590948542752567/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (85005651556820463043993590948542752567/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (852078306241550611523057595430470499987/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (852078306241550611523057595430470499987/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0499.rows BesselBatch0499.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (1702134821809755241962993504915898025657/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1702134821809755241962993504915898025657/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0141 BracketBatch0008.bracket0142 (1702134821809755241962993504915898025657/20000000000000000000000000000000000000000) (39802532071547945466848330655940229/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0141 BracketBatch0008.bracket0142
  (1702134821809755241962993504915898025657/20000000000000000000000000000000000000000) (39802532071547945466848330655940229/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0141
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0142
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (53254894140096913220191099714404406249/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (53254894140096913220191099714404406249/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (427050100432235254808675853108730867183/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (427050100432235254808675853108730867183/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (34123570142120422422808186032958644687/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34123570142120422422808186032958644687/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0142 BracketBatch0008.bracket0143 (34123570142120422422808186032958644687/400000000000000000000000000000000000000) (40184200128036220986271095652128983/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0142 BracketBatch0008.bracket0143
  (34123570142120422422808186032958644687/400000000000000000000000000000000000000) (40184200128036220986271095652128983/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0142
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0143
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (854100200864470509617351706217461734363/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (854100200864470509617351706217461734363/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0022.rows BesselBatch0022.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (171224439938353522372305697696669670049/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (171224439938353522372305697696669670049/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0500.rows BesselBatch0500.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (6680556252172805162026875760550039393/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6680556252172805162026875760550039393/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0017.rows ScalarLogs0017.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0008.bracket0143 BracketBatch0009.bracket0144 (6680556252172805162026875760550039393/78125000000000000000000000000000000000) (40568583196209858068024197106760403/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0008.bracket0143 BracketBatch0009.bracket0144
  (6680556252172805162026875760550039393/78125000000000000000000000000000000000) (40568583196209858068024197106760403/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0143
