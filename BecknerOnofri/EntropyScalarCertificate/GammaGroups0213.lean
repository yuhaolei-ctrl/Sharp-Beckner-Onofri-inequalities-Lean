module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0266
public import BecknerOnofri.EntropyScalarCertificate.Bessel0267
public import BecknerOnofri.EntropyScalarCertificate.Bessel0622
public import BecknerOnofri.EntropyScalarCertificate.Brackets0106
public import BecknerOnofri.EntropyScalarCertificate.Brackets0107
public import BecknerOnofri.EntropyScalarCertificate.Logs0213
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1704
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (4970209507143686390045290616123656198021/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4970209507143686390045290616123656198021/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (3978735011201101046363021722114924999083/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3978735011201101046363021722114924999083/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (39774513084580250791996271075069249787499/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39774513084580250791996271075069249787499/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1704 BracketBatch0106.bracket1705 (39774513084580250791996271075069249787499/20000000000000000000000000000000000000000) (397673297170501092924274715538766930813/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1704 BracketBatch0106.bracket1705
  (39774513084580250791996271075069249787499/20000000000000000000000000000000000000000) (397673297170501092924274715538766930813/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1704
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1705
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (4973418764001376307953777152643656248853/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4973418764001376307953777152643656248853/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (19906531113456711334970854758522206981701/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19906531113456711334970854758522206981701/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (39800206169462216566785963369096831977113/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39800206169462216566785963369096831977113/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1705 BracketBatch0106.bracket1706 (39800206169462216566785963369096831977113/20000000000000000000000000000000000000000) (159201030260020265207295727262565405303/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1705 BracketBatch0106.bracket1706
  (39800206169462216566785963369096831977113/20000000000000000000000000000000000000000) (159201030260020265207295727262565405303/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1705
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1706
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (9953265556728355667485427379261103490849/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9953265556728355667485427379261103490849/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (9959703122242974630864122862231032581951/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9959703122242974630864122862231032581951/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (24891210848714162872936937801865170091/12500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (24891210848714162872936937801865170091/12500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1706 BracketBatch0106.bracket1707 (24891210848714162872936937801865170091/12500000000000000000000000000000000000) (99583057573636944031770157569409345741/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1706 BracketBatch0106.bracket1707
  (24891210848714162872936937801865170091/12500000000000000000000000000000000000) (99583057573636944031770157569409345741/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1706
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1707
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (19919406244485949261728245724462065163899/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19919406244485949261728245724462065163899/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (3986460098555475028090202684366814713351/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3986460098555475028090202684366814713351/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (19925853368631662201089629573148069365327/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19925853368631662201089629573148069365327/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1707 BracketBatch0106.bracket1708 (19925853368631662201089629573148069365327/10000000000000000000000000000000000000000) (49832782715000578047716785332107124397/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1707 BracketBatch0106.bracket1708
  (19925853368631662201089629573148069365327/10000000000000000000000000000000000000000) (49832782715000578047716785332107124397/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1707
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1708
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0266.rows BesselBatch0266.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (622884390399292973139094169432314798961/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (622884390399292973139094169432314798961/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (9972606951071080441093302370594893794949/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9972606951071080441093302370594893794949/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (797550287898390720452752363260477223133/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (797550287898390720452752363260477223133/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1708 BracketBatch0106.bracket1709 (797550287898390720452752363260477223133/400000000000000000000000000000000000000) (99748167634215697437465802175325892813/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1708 BracketBatch0106.bracket1709
  (797550287898390720452752363260477223133/400000000000000000000000000000000000000) (99748167634215697437465802175325892813/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1708
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1709
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (3989042780428432176437320948237957517979/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3989042780428432176437320948237957517979/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (19958146516518941117400007319531971403797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19958146516518941117400007319531971403797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (9975840104665275499896653015180439748423/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9975840104665275499896653015180439748423/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1709 BracketBatch0106.bracket1710 (9975840104665275499896653015180439748423/5000000000000000000000000000000000000000) (798646914713485627631562326937567335783/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1709 BracketBatch0106.bracket1710
  (9975840104665275499896653015180439748423/5000000000000000000000000000000000000000) (798646914713485627631562326937567335783/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1709
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1710
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (9979073258259470558700003659765985701897/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9979073258259470558700003659765985701897/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (19971098379974262032805553369439710896203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19971098379974262032805553369439710896203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (39929244896493203150205560688971682299997/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39929244896493203150205560688971682299997/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1710 BracketBatch0106.bracket1711 (39929244896493203150205560688971682299997/20000000000000000000000000000000000000000) (19982731139622338522509614135828912483/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1710 BracketBatch0106.bracket1711
  (39929244896493203150205560688971682299997/20000000000000000000000000000000000000000) (19982731139622338522509614135828912483/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1710
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1711
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (99855491899871310164027766847198554481/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (99855491899871310164027766847198554481/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0267.rows BesselBatch0267.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2498008692087879014765084135051684369883/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2498008692087879014765084135051684369883/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0622.rows BesselBatch0622.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (1248598997396165442216444576557912057977/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1248598997396165442216444576557912057977/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0213.rows ScalarLogs0213.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0106.bracket1711 BracketBatch0107.bracket1712 (1248598997396165442216444576557912057977/625000000000000000000000000000000000000) (159994466983184338757762546561719157869/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0106.bracket1711 BracketBatch0107.bracket1712
  (1248598997396165442216444576557912057977/625000000000000000000000000000000000000) (159994466983184338757762546561719157869/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1711
