import BecknerOnofri.EntropyScalarCertificate.Bessel0398
import BecknerOnofri.EntropyScalarCertificate.Bessel0399
import BecknerOnofri.EntropyScalarCertificate.Bessel0400
import BecknerOnofri.EntropyScalarCertificate.Bessel0688
import BecknerOnofri.EntropyScalarCertificate.Brackets0159
import BecknerOnofri.EntropyScalarCertificate.Brackets0160
import BecknerOnofri.EntropyScalarCertificate.Logs0319
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2552
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (15387920482310529565883150066957538278589/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15387920482310529565883150066957538278589/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (192938887542173816368900999178344345175597/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (192938887542173816368900999178344345175597/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (770575787142110871884880750030627147315919/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (770575787142110871884880750030627147315919/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2552 BracketBatch0159.bracket2553 (770575787142110871884880750030627147315919/20000000000000000000000000000000000000000) (4659827227818239119110872694826839217661/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2552 BracketBatch0159.bracket2553
  (770575787142110871884880750030627147315919/20000000000000000000000000000000000000000) (4659827227818239119110872694826839217661/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2552
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2553
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (385877775084347632737801998356688690351191/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (385877775084347632737801998356688690351191/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (387064820842090299173872757052749311313867/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (387064820842090299173872757052749311313867/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (386471297963218965955837377704719000832529/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (386471297963218965955837377704719000832529/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2553 BracketBatch0159.bracket2554 (386471297963218965955837377704719000832529/10000000000000000000000000000000000000000) (932862249442147559123022543298002448117/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2553 BracketBatch0159.bracket2554
  (386471297963218965955837377704719000832529/10000000000000000000000000000000000000000) (932862249442147559123022543298002448117/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2553
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2554
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (48383102605261287396734094631593663914233/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (48383102605261287396734094631593663914233/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (388259216972418638752720674041892867895877/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (388259216972418638752720674041892867895877/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (775324037814508937926593431094642179209741/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (775324037814508937926593431094642179209741/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2554 BracketBatch0159.bracket2555 (775324037814508937926593431094642179209741/20000000000000000000000000000000000000000) (4668809690499797356471253668030436681047/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2554 BracketBatch0159.bracket2555
  (775324037814508937926593431094642179209741/20000000000000000000000000000000000000000) (4668809690499797356471253668030436681047/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2554
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2555
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (194129608486209319376360337020946433947937/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (194129608486209319376360337020946433947937/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (194730515978513121435817857602957639049531/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (194730515978513121435817857602957639049531/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (97215031116180610203044548655976018249367/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (97215031116180610203044548655976018249367/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2555 BracketBatch0159.bracket2556 (97215031116180610203044548655976018249367/2500000000000000000000000000000000000000) (4673322643206595350927535346720486893049/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2555 BracketBatch0159.bracket2556
  (97215031116180610203044548655976018249367/2500000000000000000000000000000000000000) (4673322643206595350927535346720486893049/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2555
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2556
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (389461031957026242871635715205915278099059/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (389461031957026242871635715205915278099059/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (12208447972842536014048641786366500584671/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12208447972842536014048641786366500584671/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (780131367087987395321192252369643296808531/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (780131367087987395321192252369643296808531/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2556 BracketBatch0159.bracket2557 (780131367087987395321192252369643296808531/20000000000000000000000000000000000000000) (1169462547895958228490140518992632900543/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2556 BracketBatch0159.bracket2557
  (780131367087987395321192252369643296808531/20000000000000000000000000000000000000000) (1169462547895958228490140518992632900543/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2556
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2557
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (390670335130961152449556537163728018709469/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (390670335130961152449556537163728018709469/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (391887196695959521194272686303422122816471/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (391887196695959521194272686303422122816471/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (39127876591346033682191461173357507076297/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39127876591346033682191461173357507076297/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2557 BracketBatch0159.bracket2558 (39127876591346033682191461173357507076297/1000000000000000000000000000000000000000) (1170598105655911777841954424427426102923/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2557 BracketBatch0159.bracket2558
  (39127876591346033682191461173357507076297/1000000000000000000000000000000000000000) (1170598105655911777841954424427426102923/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2557
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2558
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (97971799173989880298568171575855530704117/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (97971799173989880298568171575855530704117/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (393111687734030068774344371457052313902367/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (393111687734030068774344371457052313902367/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (156999776885997917993723411552094887343767/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (156999776885997917993723411552094887343767/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2558 BracketBatch0159.bracket2559 (156999776885997917993723411552094887343767/4000000000000000000000000000000000000000) (4686949424065621132869419448789841079111/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2558 BracketBatch0159.bracket2559
  (156999776885997917993723411552094887343767/4000000000000000000000000000000000000000) (4686949424065621132869419448789841079111/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2558
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2559
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0399.rows BesselBatch0399.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (98277921933507517193586092864263078475591/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (98277921933507517193586092864263078475591/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0400.rows BesselBatch0400.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (394343880221294844428233587312314015409097/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (394343880221294844428233587312314015409097/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (787455567955324913202577958769366329311461/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (787455567955324913202577958769366329311461/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0319.rows ScalarLogs0319.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2559 BracketBatch0160.bracket2560 (787455567955324913202577958769366329311461/20000000000000000000000000000000000000000) (293220080275305846229910784663081801011/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2559 BracketBatch0160.bracket2560
  (787455567955324913202577958769366329311461/20000000000000000000000000000000000000000) (293220080275305846229910784663081801011/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2559
