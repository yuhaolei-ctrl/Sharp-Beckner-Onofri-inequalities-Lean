module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0448
public import BecknerOnofri.EntropyScalarCertificate.Bessel0449
public import BecknerOnofri.EntropyScalarCertificate.Bessel0450
public import BecknerOnofri.EntropyScalarCertificate.Bessel0713
public import BecknerOnofri.EntropyScalarCertificate.Brackets0179
public import BecknerOnofri.EntropyScalarCertificate.Brackets0180
public import BecknerOnofri.EntropyScalarCertificate.Logs0359
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2872
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (68609095477849007653071793361155952356947/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (68609095477849007653071793361155952356947/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (550077694496689884865547387257139008600471/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (550077694496689884865547387257139008600471/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (1098950458319481946090121734146386627456047/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1098950458319481946090121734146386627456047/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2872 BracketBatch0179.bracket2873 (1098950458319481946090121734146386627456047/10000000000000000000000000000000000000000) (625708583200432249919227849201016931669/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2872 BracketBatch0179.bracket2873
  (1098950458319481946090121734146386627456047/10000000000000000000000000000000000000000) (625708583200432249919227849201016931669/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2872
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2873
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0448.rows BesselBatch0448.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1100155388993379769731094774514278017200939/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1100155388993379769731094774514278017200939/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1102575866512477183384290901525094414593161/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1102575866512477183384290901525094414593161/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (22027312555058569531153856760393724317941/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22027312555058569531153856760393724317941/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2873 BracketBatch0179.bracket2874 (22027312555058569531153856760393724317941/200000000000000000000000000000000000000) (1252092642485026817515269030042185810541/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2873 BracketBatch0179.bracket2874
  (22027312555058569531153856760393724317941/200000000000000000000000000000000000000) (1252092642485026817515269030042185810541/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2873
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2874
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (551287933256238591692145450762547207296579/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (551287933256238591692145450762547207296579/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1105007030508644967921576620310628871188887/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1105007030508644967921576620310628871188887/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (441516579404224430261173504367144657156409/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (441516579404224430261173504367144657156409/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2874 BracketBatch0179.bracket2875 (441516579404224430261173504367144657156409/4000000000000000000000000000000000000000) (782981006089782336031664507203823642259/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2874 BracketBatch0179.bracket2875
  (441516579404224430261173504367144657156409/4000000000000000000000000000000000000000) (782981006089782336031664507203823642259/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2874
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2875
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (276251757627161241980394155077657217797221/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (276251757627161241980394155077657217797221/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1107448951909826671380396065360266174979033/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1107448951909826671380396065360266174979033/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (2212455982418471639301972685670895046167917/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2212455982418471639301972685670895046167917/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2875 BracketBatch0179.bracket2876 (2212455982418471639301972685670895046167917/20000000000000000000000000000000000000000) (783405046506843017336016001046299594281/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2875 BracketBatch0179.bracket2876
  (2212455982418471639301972685670895046167917/20000000000000000000000000000000000000000) (783405046506843017336016001046299594281/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2875
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2876
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (110744895190982667138039606536026617497903/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (110744895190982667138039606536026617497903/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1109901702273038511969396723929745985024399/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1109901702273038511969396723929745985024399/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (2217350654182865183349792789290012160003429/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2217350654182865183349792789290012160003429/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2876 BracketBatch0179.bracket2877 (2217350654182865183349792789290012160003429/20000000000000000000000000000000000000000) (6270640213792675884941950063006559768107/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2876 BracketBatch0179.bracket2877
  (2217350654182865183349792789290012160003429/20000000000000000000000000000000000000000) (6270640213792675884941950063006559768107/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2876
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2877
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (277475425568259627992349180982436496256099/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (277475425568259627992349180982436496256099/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (278091338447839768600912379899683361642991/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (278091338447839768600912379899683361642991/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (55556676401609939659326156088211985789909/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (55556676401609939659326156088211985789909/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2877 BracketBatch0179.bracket2878 (55556676401609939659326156088211985789909/500000000000000000000000000000000000000) (784255950684821912066053533807315357933/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2877 BracketBatch0179.bracket2878
  (55556676401609939659326156088211985789909/500000000000000000000000000000000000000) (784255950684821912066053533807315357933/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2877
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2878
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1112365353791359074403649519598733446571961/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1112365353791359074403649519598733446571961/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1114839979301012409754370726161916382312431/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1114839979301012409754370726161916382312431/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (278400666636546435519752530720081228610549/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (278400666636546435519752530720081228610549/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2878 BracketBatch0179.bracket2879 (278400666636546435519752530720081228610549/2500000000000000000000000000000000000000) (1255492515769761905722615742820627573913/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2878 BracketBatch0179.bracket2879
  (278400666636546435519752530720081228610549/2500000000000000000000000000000000000000) (1255492515769761905722615742820627573913/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2878
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2879
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0449.rows BesselBatch0449.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (278709994825253102438592681540479095578107/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (278709994825253102438592681540479095578107/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0450.rows BesselBatch0450.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (558662826144272999121529901475911069491757/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (558662826144272999121529901475911069491757/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0713.rows BesselBatch0713.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (1116082815794779203998715264556869260647971/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1116082815794779203998715264556869260647971/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0359.rows ScalarLogs0359.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0179.bracket2879 BracketBatch0180.bracket2880 (1116082815794779203998715264556869260647971/10000000000000000000000000000000000000000) (6280885165195200221821333374421902448133/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0179.bracket2879 BracketBatch0180.bracket2880
  (1116082815794779203998715264556869260647971/10000000000000000000000000000000000000000) (6280885165195200221821333374421902448133/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2879
