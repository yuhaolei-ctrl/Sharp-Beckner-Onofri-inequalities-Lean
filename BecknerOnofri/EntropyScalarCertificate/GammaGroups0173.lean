import BecknerOnofri.EntropyScalarCertificate.Bessel0216
import BecknerOnofri.EntropyScalarCertificate.Bessel0217
import BecknerOnofri.EntropyScalarCertificate.Bessel0597
import BecknerOnofri.EntropyScalarCertificate.Brackets0086
import BecknerOnofri.EntropyScalarCertificate.Brackets0087
import BecknerOnofri.EntropyScalarCertificate.Logs0173
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1384
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (4139036012198632026147119568498354018643/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4139036012198632026147119568498354018643/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (4141146573061833269097852738726748903933/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4141146573061833269097852738726748903933/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (517511411578779080952810769201568932661/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (517511411578779080952810769201568932661/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1384 BracketBatch0086.bracket1385 (517511411578779080952810769201568932661/312500000000000000000000000000000000000) (617451240711791137141162262310267740843/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1384 BracketBatch0086.bracket1385
  (517511411578779080952810769201568932661/312500000000000000000000000000000000000) (617451240711791137141162262310267740843/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1384
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1385
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (16564586292247333076391410954906995615729/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16564586292247333076391410954906995615729/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (16573038305033898232774196886320001733739/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16573038305033898232774196886320001733739/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (8284406149320307827291401960306749337367/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8284406149320307827291401960306749337367/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1385 BracketBatch0086.bracket1386 (8284406149320307827291401960306749337367/5000000000000000000000000000000000000000) (38620036206796090504815189622114169927/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1385 BracketBatch0086.bracket1386
  (8284406149320307827291401960306749337367/5000000000000000000000000000000000000000) (38620036206796090504815189622114169927/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1385
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1386
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (2071629788129237279096774610790000216717/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2071629788129237279096774610790000216717/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (8290750052870852994967648466192319460549/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8290750052870852994967648466192319460549/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (16577269205387802111354746909352320327417/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16577269205387802111354746909352320327417/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1386 BracketBatch0086.bracket1387 (16577269205387802111354746909352320327417/10000000000000000000000000000000000000000) (618390378267480956982241949898439111389/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1386 BracketBatch0086.bracket1387
  (16577269205387802111354746909352320327417/10000000000000000000000000000000000000000) (618390378267480956982241949898439111389/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1386
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1387
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (3316300021148341197987059386476927784219/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3316300021148341197987059386476927784219/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (16589971713003889338861279611544014047079/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16589971713003889338861279611544014047079/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (16585735909372797664398288271964326484087/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16585735909372797664398288271964326484087/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1387 BracketBatch0086.bracket1388 (16585735909372797664398288271964326484087/10000000000000000000000000000000000000000) (309430319127346643594631943401933081273/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1387 BracketBatch0086.bracket1388
  (16585735909372797664398288271964326484087/10000000000000000000000000000000000000000) (309430319127346643594631943401933081273/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1387
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1388
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0216.rows BesselBatch0216.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (4147492928250972334715319902886003511769/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4147492928250972334715319902886003511769/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (8299226572749682884425149838248831041207/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8299226572749682884425149838248831041207/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (3318842485850325510771157928804167612949/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3318842485850325510771157928804167612949/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1388 BracketBatch0086.bracket1389 (3318842485850325510771157928804167612949/2000000000000000000000000000000000000000) (619331359938281347349325491442596259927/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1388 BracketBatch0086.bracket1389
  (3318842485850325510771157928804167612949/2000000000000000000000000000000000000000) (619331359938281347349325491442596259927/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1388
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1389
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (16598453145499365768850299676497662082411/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16598453145499365768850299676497662082411/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (8303472210976485822536621880869666908061/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8303472210976485822536621880869666908061/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (33205397567452337413923543438236995898533/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33205397567452337413923543438236995898533/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1389 BracketBatch0086.bracket1390 (33205397567452337413923543438236995898533/20000000000000000000000000000000000000000) (619802543987389775242008754891767589741/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1389 BracketBatch0086.bracket1390
  (33205397567452337413923543438236995898533/20000000000000000000000000000000000000000) (619802543987389775242008754891767589741/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1389
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1390
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (16606944421952971645073243761739333816119/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16606944421952971645073243761739333816119/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (16615445561135597041946823427451389036691/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16615445561135597041946823427451389036691/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (3322238998308856868702006718919072285281/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3322238998308856868702006718919072285281/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1390 BracketBatch0086.bracket1391 (3322238998308856868702006718919072285281/2000000000000000000000000000000000000000) (124054838214480677247179522297340096559/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1390 BracketBatch0086.bracket1391
  (3322238998308856868702006718919072285281/2000000000000000000000000000000000000000) (124054838214480677247179522297340096559/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1390
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1391
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1038465347570974815121676464215711814793/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1038465347570974815121676464215711814793/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0217.rows BesselBatch0217.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (259749321591630016157828698428457584891/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (259749321591630016157828698428457584891/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0597.rows BesselBatch0597.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (2077462633937494879752991257929542154357/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2077462633937494879752991257929542154357/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0173.rows ScalarLogs0173.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0086.bracket1391 BracketBatch0087.bracket1392 (2077462633937494879752991257929542154357/1250000000000000000000000000000000000000) (15518657546623740660245744841047692191/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0086.bracket1391 BracketBatch0087.bracket1392
  (2077462633937494879752991257929542154357/1250000000000000000000000000000000000000) (15518657546623740660245744841047692191/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1391
