import BecknerOnofri.EntropyScalarCertificate.Bessel0050
import BecknerOnofri.EntropyScalarCertificate.Bessel0051
import BecknerOnofri.EntropyScalarCertificate.Bessel0513
import BecknerOnofri.EntropyScalarCertificate.Bessel0514
import BecknerOnofri.EntropyScalarCertificate.Brackets0020
import BecknerOnofri.EntropyScalarCertificate.Logs0040
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0320
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (151731973816538874104671304666959367943/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (151731973816538874104671304666959367943/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (607950161204766582891757523738518055983/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (607950161204766582891757523738518055983/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (242975611294184415862088548481271105551/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (242975611294184415862088548481271105551/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0320 BracketBatch0020.bracket0321 (242975611294184415862088548481271105551/2000000000000000000000000000000000000000) (164802101306784223637179702918087777/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0320 BracketBatch0020.bracket0321
  (242975611294184415862088548481271105551/2000000000000000000000000000000000000000) (164802101306784223637179702918087777/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0320
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0321
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1215900322409533165783515047477036111963/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1215900322409533165783515047477036111963/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (243589001032575838669155130778719994129/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (243589001032575838669155130778719994129/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0513.rows BesselBatch0513.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (152115332973275772445580668835664755163/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (152115332973275772445580668835664755163/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0321 BracketBatch0020.bracket0322 (152115332973275772445580668835664755163/1250000000000000000000000000000000000000) (16590493753839588201717362310534571/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0321 BracketBatch0020.bracket0322
  (152115332973275772445580668835664755163/1250000000000000000000000000000000000000) (16590493753839588201717362310534571/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0321
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0322
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (608972502581439596672887826946799985321/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (608972502581439596672887826946799985321/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1219989839063001746197249314603688621337/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1219989839063001746197249314603688621337/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (2437934844225880939543024968497288591979/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2437934844225880939543024968497288591979/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0322 BracketBatch0020.bracket0323 (2437934844225880939543024968497288591979/20000000000000000000000000000000000000000) (83506651245051941288670578008170693/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0322 BracketBatch0020.bracket0323
  (2437934844225880939543024968497288591979/20000000000000000000000000000000000000000) (83506651245051941288670578008170693/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0322
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0323
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (609994919531500873098624657301844310667/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (609994919531500873098624657301844310667/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (305508706095165033274591951592364140449/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (305508706095165033274591951592364140449/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (244202466344366187929561712097314518313/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (244202466344366187929561712097314518313/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0323 BracketBatch0020.bracket0324 (244202466344366187929561712097314518313/2000000000000000000000000000000000000000) (2626987730823172126576265406594031/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0323 BracketBatch0020.bracket0324
  (244202466344366187929561712097314518313/2000000000000000000000000000000000000000) (2626987730823172126576265406594031/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0323
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0324
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1222034824380660133098367806369456561793/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1222034824380660133098367806369456561793/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (24481599227734410239778776996947890453/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24481599227734410239778776996947890453/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (2446114785767380645087306656216851084443/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2446114785767380645087306656216851084443/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0324 BracketBatch0020.bracket0325 (2446114785767380645087306656216851084443/20000000000000000000000000000000000000000) (84623346514778797943755996562977897/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0324 BracketBatch0020.bracket0325
  (2446114785767380645087306656216851084443/20000000000000000000000000000000000000000) (84623346514778797943755996562977897/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0324
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0325
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1224079961386720511988938849847394522647/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1224079961386720511988938849847394522647/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1226125250352156101264519741776892669039/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1226125250352156101264519741776892669039/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1225102605869438306626729295812143595843/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1225102605869438306626729295812143595843/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0325 BracketBatch0020.bracket0326 (1225102605869438306626729295812143595843/10000000000000000000000000000000000000000) (170371755936810864576579476360286803/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0325 BracketBatch0020.bracket0326
  (1225102605869438306626729295812143595843/10000000000000000000000000000000000000000) (170371755936810864576579476360286803/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0325
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0326
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0050.rows BesselBatch0050.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (306531312588039025316129935444223167259/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (306531312588039025316129935444223167259/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1228170691548047391237534671900651949411/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1228170691548047391237534671900651949411/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (2454295941900203492502054413677544618447/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2454295941900203492502054413677544618447/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0326 BracketBatch0020.bracket0327 (2454295941900203492502054413677544618447/20000000000000000000000000000000000000000) (21437802775399302378355735418684683/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0326 BracketBatch0020.bracket0327
  (2454295941900203492502054413677544618447/20000000000000000000000000000000000000000) (21437802775399302378355735418684683/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0326
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0327
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (38380334110876480976172958496895373419/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38380334110876480976172958496895373419/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0051.rows BesselBatch0051.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1537770356556977944729434488186296319/12500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1537770356556977944729434488186296319/12500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0514.rows BesselBatch0514.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (38412296512400464797204410350776390697/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38412296512400464797204410350776390697/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0040.rows ScalarLogs0040.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0020.bracket0327 BracketBatch0020.bracket0328 (38412296512400464797204410350776390697/312500000000000000000000000000000000000) (172638710570137653266289188073104411/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0020.bracket0327 BracketBatch0020.bracket0328
  (38412296512400464797204410350776390697/312500000000000000000000000000000000000) (172638710570137653266289188073104411/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0327
