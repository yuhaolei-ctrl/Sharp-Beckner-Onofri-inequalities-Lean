module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0276
public import BecknerOnofri.EntropyScalarCertificate.Bessel0277
public import BecknerOnofri.EntropyScalarCertificate.Bessel0627
public import BecknerOnofri.EntropyScalarCertificate.Brackets0110
public import BecknerOnofri.EntropyScalarCertificate.Brackets0111
public import BecknerOnofri.EntropyScalarCertificate.Logs0221
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1768
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (10371335524970246172149762648757020832859/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10371335524970246172149762648757020832859/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (10378409691085524337759241453155433714017/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10378409691085524337759241453155433714017/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (5187436304013942627477251025478113636719/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5187436304013942627477251025478113636719/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1768 BracketBatch0110.bracket1769 (5187436304013942627477251025478113636719/2500000000000000000000000000000000000000) (839063267326971883156602569690927957633/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1768 BracketBatch0110.bracket1769
  (5187436304013942627477251025478113636719/2500000000000000000000000000000000000000) (839063267326971883156602569690927957633/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1768
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1769
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (20756819382171048675518482906310867428031/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20756819382171048675518482906310867428031/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1038549490354841130930345853045035748377/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1038549490354841130930345853045035748377/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (41527809189267871294125399967211582395571/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41527809189267871294125399967211582395571/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1769 BracketBatch0110.bracket1770 (41527809189267871294125399967211582395571/20000000000000000000000000000000000000000) (209943133056946124260604166152347915957/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1769 BracketBatch0110.bracket1770
  (41527809189267871294125399967211582395571/20000000000000000000000000000000000000000) (209943133056946124260604166152347915957/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1769
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1770
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (20770989807096822618606917060900714967537/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20770989807096822618606917060900714967537/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2598147797169824183216177497216569127977/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2598147797169824183216177497216569127977/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (41556172184455416084336337038633267991353/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41556172184455416084336337038633267991353/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1770 BracketBatch0110.bracket1771 (41556172184455416084336337038633267991353/20000000000000000000000000000000000000000) (840482632426314175157961979959799997173/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1770 BracketBatch0110.bracket1771
  (41556172184455416084336337038633267991353/20000000000000000000000000000000000000000) (840482632426314175157961979959799997173/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1770
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1771
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (20785182377358593465729419977732553023813/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20785182377358593465729419977732553023813/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (20799397145756453464226930808211830399851/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20799397145756453464226930808211830399851/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (2599036220194690433122271924121523963979/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2599036220194690433122271924121523963979/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1771 BracketBatch0110.bracket1772 (2599036220194690433122271924121523963979/1250000000000000000000000000000000000000) (420596784651389154122267253149355960209/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1771 BracketBatch0110.bracket1772
  (2599036220194690433122271924121523963979/1250000000000000000000000000000000000000) (420596784651389154122267253149355960209/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1771
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1772
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (2599924643219556683028366351026478799981/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2599924643219556683028366351026478799981/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (20813634165250396317246541909550341829609/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20813634165250396317246541909550341829609/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (41613031311006849781473472717762172229457/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41613031311006849781473472717762172229457/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1772 BracketBatch0110.bracket1773 (41613031311006849781473472717762172229457/20000000000000000000000000000000000000000) (420952672120056945306394554156805485139/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1772 BracketBatch0110.bracket1773
  (41613031311006849781473472717762172229457/20000000000000000000000000000000000000000) (420952672120056945306394554156805485139/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1772
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1773
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (10406817082625198158623270954775170914803/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10406817082625198158623270954775170914803/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (20827893488960908339992165356788774023617/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20827893488960908339992165356788774023617/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (41641527654211304657238707266339115853223/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41641527654211304657238707266339115853223/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1773 BracketBatch0110.bracket1774 (41641527654211304657238707266339115853223/20000000000000000000000000000000000000000) (421308979311991982367702817017027640249/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1773 BracketBatch0110.bracket1774
  (41641527654211304657238707266339115853223/20000000000000000000000000000000000000000) (421308979311991982367702817017027640249/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1773
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1774
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (10413946744480454169996082678394387011807/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10413946744480454169996082678394387011807/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (4168435034033912457236241881840292213563/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4168435034033912457236241881840292213563/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (41670068659130470626173374765990235091429/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41670068659130470626173374765990235091429/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1774 BracketBatch0110.bracket1775 (41670068659130470626173374765990235091429/20000000000000000000000000000000000000000) (421665706921392045519511847933709976921/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1774 BracketBatch0110.bracket1775
  (41670068659130470626173374765990235091429/20000000000000000000000000000000000000000) (421665706921392045519511847933709976921/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1774
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1775
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (5210543792542390571545302352300365266953/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5210543792542390571545302352300365266953/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0277.rows BesselBatch0277.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (20856479262319613859386289447129881441239/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20856479262319613859386289447129881441239/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (41698654432489176145567498856331342509051/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41698654432489176145567498856331342509051/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0221.rows ScalarLogs0221.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1775 BracketBatch0111.bracket1776 (41698654432489176145567498856331342509051/20000000000000000000000000000000000000000) (844045711287648843061971553084845442373/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1775 BracketBatch0111.bracket1776
  (41698654432489176145567498856331342509051/20000000000000000000000000000000000000000) (844045711287648843061971553084845442373/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1775
