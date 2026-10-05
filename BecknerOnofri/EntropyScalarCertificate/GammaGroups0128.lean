import BecknerOnofri.EntropyScalarCertificate.Bessel0160
import BecknerOnofri.EntropyScalarCertificate.Bessel0161
import BecknerOnofri.EntropyScalarCertificate.Bessel0568
import BecknerOnofri.EntropyScalarCertificate.Bessel0569
import BecknerOnofri.EntropyScalarCertificate.Brackets0064
import BecknerOnofri.EntropyScalarCertificate.Logs0128
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1024
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (5891351763638512455280972370457982659739/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5891351763638512455280972370457982659739/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (2953633364609153107478754659083422798331/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2953633364609153107478754659083422798331/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (11798618492856818670238481688624828256401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11798618492856818670238481688624828256401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1024 BracketBatch0064.bracket1025 (11798618492856818670238481688624828256401/20000000000000000000000000000000000000000) (57378590864096237401733868097315864237/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1024 BracketBatch0064.bracket1025
  (11798618492856818670238481688624828256401/20000000000000000000000000000000000000000) (57378590864096237401733868097315864237/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1024
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1025
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (5907266729218306214957509318166845596659/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5907266729218306214957509318166845596659/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (5923217385759258192843131737971902881273/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5923217385759258192843131737971902881273/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0568.rows BesselBatch0568.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (2957621028744391101950160264034687119483/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2957621028744391101950160264034687119483/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1025 BracketBatch0064.bracket1026 (2957621028744391101950160264034687119483/5000000000000000000000000000000000000000) (11301767244857475311857781760438449/1953125000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1025 BracketBatch0064.bracket1026
  (2957621028744391101950160264034687119483/5000000000000000000000000000000000000000) (11301767244857475311857781760438449/1953125000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1025
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1026
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (592321738575925819284313173797190288127/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (592321738575925819284313173797190288127/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (5939203949093862140942548488927802322977/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5939203949093862140942548488927802322977/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (11862421334853120333785680226899705204247/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11862421334853120333785680226899705204247/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1026 BracketBatch0064.bracket1027 (11862421334853120333785680226899705204247/20000000000000000000000000000000000000000) (7294353818139077477181092545113880487/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1026 BracketBatch0064.bracket1027
  (11862421334853120333785680226899705204247/20000000000000000000000000000000000000000) (7294353818139077477181092545113880487/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1026
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1027
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (2969601974546931070471274244463901161487/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2969601974546931070471274244463901161487/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (5955226636756465716330325954401920065113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5955226636756465716330325954401920065113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (11894430585850327857272874443329722388087/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11894430585850327857272874443329722388087/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1027 BracketBatch0064.bracket1028 (11894430585850327857272874443329722388087/20000000000000000000000000000000000000000) (919499317989265723549444633220171159/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1027 BracketBatch0064.bracket1028
  (11894430585850327857272874443329722388087/20000000000000000000000000000000000000000) (919499317989265723549444633220171159/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1027
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1028
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (595522663675646571633032595440192006511/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (595522663675646571633032595440192006511/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (238851426720046723244106007424040917377/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (238851426720046723244106007424040917377/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (2385302460951526759486595228000588599907/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2385302460951526759486595228000588599907/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1028 BracketBatch0064.bracket1029 (2385302460951526759486595228000588599907/4000000000000000000000000000000000000000) (29672222275384312628789677763632789857/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1028 BracketBatch0064.bracket1029
  (2385302460951526759486595228000588599907/4000000000000000000000000000000000000000) (29672222275384312628789677763632789857/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1028
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1029
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (2985642834000584040551325092800511467211/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2985642834000584040551325092800511467211/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1496845315954986477496667669573223617407/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1496845315954986477496667669573223617407/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (239173338636422279821786417277878348081/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (239173338636422279821786417277878348081/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1029 BracketBatch0064.bracket1030 (239173338636422279821786417277878348081/400000000000000000000000000000000000000) (5984431408845098985492808021220882119/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1029 BracketBatch0064.bracket1030
  (239173338636422279821786417277878348081/400000000000000000000000000000000000000) (5984431408845098985492808021220882119/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1029
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1030
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0160.rows BesselBatch0160.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (47899050110559567279893365426343155757/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (47899050110559567279893365426343155757/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (6003513646961011247634889964882465052041/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6003513646961011247634889964882465052041/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (5995447455390478578810780321587679760833/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5995447455390478578810780321587679760833/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1030 BracketBatch0064.bracket1031 (5995447455390478578810780321587679760833/10000000000000000000000000000000000000000) (60347584016683260595938391093261587149/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1030 BracketBatch0064.bracket1031
  (5995447455390478578810780321587679760833/10000000000000000000000000000000000000000) (60347584016683260595938391093261587149/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1030
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1031
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (3001756823480505623817444982441232526019/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3001756823480505623817444982441232526019/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0161.rows BesselBatch0161.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (6019683041947404717140314809497008067683/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6019683041947404717140314809497008067683/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0569.rows BesselBatch0569.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (12023196688908415964775204774379473119721/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12023196688908415964775204774379473119721/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0128.rows ScalarLogs0128.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0064.bracket1031 BracketBatch0064.bracket1032 (12023196688908415964775204774379473119721/20000000000000000000000000000000000000000) (60854273496028193874203386393332462121/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0064.bracket1031 BracketBatch0064.bracket1032
  (12023196688908415964775204774379473119721/20000000000000000000000000000000000000000) (60854273496028193874203386393332462121/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1031
