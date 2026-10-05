module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0456
public import BecknerOnofri.EntropyScalarCertificate.Bessel0457
public import BecknerOnofri.EntropyScalarCertificate.Bessel0717
public import BecknerOnofri.EntropyScalarCertificate.Brackets0182
public import BecknerOnofri.EntropyScalarCertificate.Brackets0183
public import BecknerOnofri.EntropyScalarCertificate.Logs0365
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2920
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (613372020367337136806065299862506252686309/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (613372020367337136806065299862506252686309/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1229755063685868874126662317364930162179597/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1229755063685868874126662317364930162179597/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (491299820884108629547758583417988533510443/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (491299820884108629547758583417988533510443/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2920 BracketBatch0182.bracket2921 (491299820884108629547758583417988533510443/4000000000000000000000000000000000000000) (80352329445036639591402679960533848143/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2920 BracketBatch0182.bracket2921
  (491299820884108629547758583417988533510443/4000000000000000000000000000000000000000) (80352329445036639591402679960533848143/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2920
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2921
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (614877531842934437063331158682465081089797/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (614877531842934437063331158682465081089797/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (616390459654668367871240688965951740899447/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (616390459654668367871240688965951740899447/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (307816997874400701233642961912104205497311/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (307816997874400701233642961912104205497311/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2921 BracketBatch0182.bracket2922 (307816997874400701233642961912104205497311/2500000000000000000000000000000000000000) (1286392047867529971727698673644113868777/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2921 BracketBatch0182.bracket2922
  (307816997874400701233642961912104205497311/2500000000000000000000000000000000000000) (1286392047867529971727698673644113868777/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2921
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2922
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1232780919309336735742481377931903481798891/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1232780919309336735742481377931903481798891/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (617910858738361268691536057380592501034701/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (617910858738361268691536057380592501034701/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (2468602636786059273125553492693088483868293/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2468602636786059273125553492693088483868293/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2922 BracketBatch0182.bracket2923 (2468602636786059273125553492693088483868293/20000000000000000000000000000000000000000) (1287148662351785934800349025117184307887/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2922 BracketBatch0182.bracket2923
  (2468602636786059273125553492693088483868293/20000000000000000000000000000000000000000) (1287148662351785934800349025117184307887/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2922
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2923
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1235821717476722537383072114761185002069399/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1235821717476722537383072114761185002069399/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1238877569147509024235360128204343071607393/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1238877569147509024235360128204343071607393/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (309337410828028945202304030370691009209599/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (309337410828028945202304030370691009209599/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2923 BracketBatch0182.bracket2924 (309337410828028945202304030370691009209599/2500000000000000000000000000000000000000) (402470975924626550791948067482618483389/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2923 BracketBatch0182.bracket2924
  (309337410828028945202304030370691009209599/2500000000000000000000000000000000000000) (402470975924626550791948067482618483389/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2923
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2924
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0456.rows BesselBatch0456.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (123887756914750902423536012820434307160739/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (123887756914750902423536012820434307160739/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (248389717276502751590294957754722348889619/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (248389717276502751590294957754722348889619/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (496165231106004556437366983395590963211097/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (496165231106004556437366983395590963211097/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2924 BracketBatch0182.bracket2925 (496165231106004556437366983395590963211097/4000000000000000000000000000000000000000) (257733487625539538110039850806763823179/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2924 BracketBatch0182.bracket2925
  (496165231106004556437366983395590963211097/4000000000000000000000000000000000000000) (257733487625539538110039850806763823179/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2924
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2925
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (310487146595628439487868697193402936112023/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (310487146595628439487868697193402936112023/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1245034882357587310883373870438539591584609/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1245034882357587310883373870438539591584609/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (2486983468740101068834848659212151336032701/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2486983468740101068834848659212151336032701/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2925 BracketBatch0182.bracket2926 (2486983468740101068834848659212151336032701/20000000000000000000000000000000000000000) (32235740408791023233351000999523577487/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2925 BracketBatch0182.bracket2926
  (2486983468740101068834848659212151336032701/20000000000000000000000000000000000000000) (32235740408791023233351000999523577487/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2925
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2926
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (622517441178793655441686935219269795792303/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (622517441178793655441686935219269795792303/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (19502133927773694075464171245899988702279/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19502133927773694075464171245899988702279/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (1246585726867551865856540415088069434265231/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1246585726867551865856540415088069434265231/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2926 BracketBatch0182.bracket2927 (1246585726867551865856540415088069434265231/10000000000000000000000000000000000000000) (6450968330891434661986972848992351970687/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2926 BracketBatch0182.bracket2927
  (1246585726867551865856540415088069434265231/10000000000000000000000000000000000000000) (6450968330891434661986972848992351970687/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2926
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2927
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1248136571377516420829706959737599276945853/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1248136571377516420829706959737599276945853/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (78203360555633480818992613705042079472467/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (78203360555633480818992613705042079472467/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (99975613610706084557343551160730901940213/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (99975613610706084557343551160730901940213/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0365.rows ScalarLogs0365.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0182.bracket2927 BracketBatch0183.bracket2928 (99975613610706084557343551160730901940213/800000000000000000000000000000000000000) (161369949526271944256693276390656040369/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0182.bracket2927 BracketBatch0183.bracket2928
  (99975613610706084557343551160730901940213/800000000000000000000000000000000000000) (161369949526271944256693276390656040369/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2927
