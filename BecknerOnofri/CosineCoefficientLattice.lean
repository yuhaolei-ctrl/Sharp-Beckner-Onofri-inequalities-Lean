module

public import BecknerOnofri.GinibreSupermodularity
public import BecknerOnofri.GinibreStrictCovariance
public import BecknerOnofri.ContinuousOptimizers

@[expose] public section

/-! Actual Sobolev potentials associated to nonnegative even cosine
coefficient families. Coordinatewise maxima and minima stay in the original
admissible domain, and their true critical energies satisfy the lattice identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.CosineCoefficientLattice
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment
open ContinuousGibbs ContinuousFirstShell GinibreCovariance

def energyTerm {d : ℕ} (a : Frequency d → ℝ) (k : Frequency d) : ℝ := frequencyRadius k^d*(a k)^2

def energy {d : ℕ} (a : Frequency d → ℝ) : ℝ := ∑' k,energyTerm a k

structure Domain {d : ℕ} (a : Frequency d → ℝ) : Prop where
  nonneg : ∀ k,0≤a k
  even : ∀ k,a (-k)=a k
  zero : a 0=0
  summable : Summable a
  weighted : Summable (energyTerm a)

theorem series_re {d : ℕ} (a : Frequency d → ℝ) (ha : ∀ k,0≤a k)
    (hs : Summable a) (x : Torus d) :
    cosineSeries a id x=(absoluteFourierSeries (fun k => (a k : ℂ)) x).re := by
  have hsC := cosineSeries_summable a id ha hs
  have hx : Summable (fun k => (a k : ℂ)*UnitAddTorus.mFourier k x) := by
    apply hs.of_norm_bounded
    intro k
    simp only [norm_mul,mFourier_norm_apply,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha k),le_refl]
  trans ∑' k,a k*cosine k x
  · convert! (ContinuousMap.evalCLM ℝ x).map_tsum hsC using 1
  rw [absoluteFourierSeries,Complex.re_tsum hx]
  apply tsum_congr
  intro k
  simp [cosine_apply,Complex.mul_re]

theorem series_real {d : ℕ} (a : Frequency d → ℝ) (heven : ∀ k,a (-k)=a k) (x : Torus d) :
    (absoluteFourierSeries (fun k => (a k : ℂ)) x).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  change conj (∑' k, (a k : ℂ)*UnitAddTorus.mFourier k x)=_
  rw [Complex.conj_tsum]
  calc
    _ = ∑' k, (a (-k) : ℂ)*UnitAddTorus.mFourier (-k) x := by
      apply tsum_congr
      intro k
      rw [map_mul,heven,Complex.conj_ofReal,UnitAddTorus.mFourier_neg]
    _ = _ := (Equiv.neg (Frequency d)).tsum_eq (fun k => (a k : ℂ)*UnitAddTorus.mFourier k x)

theorem series_coefficient {d : ℕ} (a : Frequency d → ℝ) (ha : ∀ k,0≤a k)
    (hs : Summable a) (heven : ∀ k,a (-k)=a k) (k : Frequency d) :
    coefficient k (cosineSeries a id)=(a k : ℂ) := by
  have hsC : Summable (fun k => ‖(a k : ℂ)‖) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha _)] using hs
  rw [coefficient_integral]
  calc
    _ = UnitAddTorus.mFourierCoeff (absoluteFourierSeries (fun k => (a k : ℂ))) k := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        change UnitAddTorus.mFourier (-k) x*(cosineSeries a id x : ℂ)=
          UnitAddTorus.mFourier (-k) x*absoluteFourierSeries (fun k => (a k : ℂ)) x
        rw [series_re a ha hs]
        congr 1
        apply Complex.ext
        · rfl
        · exact (series_real a heven x).symm)
    _ = _ := absoluteFourierSeries_coefficient _ hsC k

def toPotential {d : ℕ} (a : Frequency d → ℝ) : TorusL2 d := toL2 d (cosineSeries a id)

theorem toPotential_coefficient {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) (k : Frequency d) :
    fourierIsometry d (toPotential a) k=(a k : ℂ) :=
  series_coefficient a ha.nonneg ha.summable ha.even k

theorem toPotential_weighted {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) (k : Frequency d) :
    weightedSquare (fourierIsometry d (toPotential a)) k=energyTerm a k := by
  simp only [weightedSquare,energyTerm,toPotential_coefficient ha,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem toPotential_admissible {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) :
    Admissible (toPotential a) := by
  refine ⟨GraphRegularity.toL2_real _, ?_, ?_⟩
  · rw [toPotential_coefficient ha,ha.zero,Complex.ofReal_zero]
  · exact ha.weighted.congr (fun k => (toPotential_weighted ha k).symm)

theorem toPotential_energy {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) :
    criticalEnergy (toPotential a)=energy a := by
  simp only [criticalEnergy,coefficientEnergy,toPotential_weighted ha,energy]

theorem toPotential_functional {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) (A : ℝ) :
    functional A (toPotential a)=logPartitionReal (cosineSeries a id)-A*energy a := by
  rw [functional,toPotential_energy ha]
  congr 2
  exact ContinuousOptimizers.partition_toL2 _

theorem Domain.min {d : ℕ} {a b : Frequency d → ℝ} (ha : Domain a) (hb : Domain b) :
    Domain (fun k => min (a k) (b k)) where
  nonneg k := le_min (ha.nonneg k) (hb.nonneg k)
  even k := by rw [ha.even,hb.even]
  zero := by rw [ha.zero,hb.zero,min_self]
  summable := ha.summable.of_nonneg_of_le (fun k => le_min (ha.nonneg k) (hb.nonneg k))
    (fun k => min_le_left _ _)
  weighted := by
    apply ha.weighted.of_nonneg_of_le
    · intro k; unfold energyTerm frequencyRadius; positivity
    · intro k
      apply mul_le_mul_of_nonneg_left _ (by unfold frequencyRadius; positivity)
      have h0 := le_min (ha.nonneg k) (hb.nonneg k)
      have h1 := min_le_left (a k) (b k)
      nlinarith

theorem Domain.max {d : ℕ} {a b : Frequency d → ℝ} (ha : Domain a) (hb : Domain b) :
    Domain (fun k => max (a k) (b k)) where
  nonneg k := (ha.nonneg k).trans (le_max_left _ _)
  even k := by rw [ha.even,hb.even]
  zero := by rw [ha.zero,hb.zero,max_self]
  summable := (ha.summable.add hb.summable).of_nonneg_of_le
    (fun k => (ha.nonneg k).trans (le_max_left _ _))
    (fun k => max_le (le_add_of_nonneg_right (hb.nonneg k)) (le_add_of_nonneg_left (ha.nonneg k)))
  weighted := by
    apply (ha.weighted.add hb.weighted).of_nonneg_of_le
    · intro k; unfold energyTerm frequencyRadius; positivity
    · intro k
      change frequencyRadius k^d*(Max.max (a k) (b k))^2≤energyTerm a k+energyTerm b k
      rcases le_total (a k) (b k) with hab | hba
      · rw [max_eq_right hab]
        exact le_add_of_nonneg_left (by unfold energyTerm frequencyRadius; positivity)
      · rw [max_eq_left hba]
        exact le_add_of_nonneg_right (by unfold energyTerm frequencyRadius; positivity)

theorem energy_lattice {d : ℕ} {a b : Frequency d → ℝ} (ha : Domain a) (hb : Domain b) :
    energy (fun k => max (a k) (b k))+energy (fun k => min (a k) (b k))=energy a+energy b := by
  rw [energy,energy,energy,energy,← (ha.max hb).weighted.tsum_add (ha.min hb).weighted,
    ← ha.weighted.tsum_add hb.weighted]
  apply tsum_congr
  intro k
  dsimp only [energyTerm]
  rcases le_total (a k) (b k) with hab | hba
  · rw [max_eq_right hab,min_eq_left hab]; ring
  · rw [max_eq_left hba,min_eq_right hba]

/-- Supermodularity holds for the actual original critical Sobolev functional. -/
theorem functional_supermodular {d : ℕ} {a b : Frequency d → ℝ}
    (ha : Domain a) (hb : Domain b) (A : ℝ) :
    functional A (toPotential a)+functional A (toPotential b)≤
      functional A (toPotential (fun k => max (a k) (b k)))+
        functional A (toPotential (fun k => min (a k) (b k))) := by
  rw [toPotential_functional ha,toPotential_functional hb,
    toPotential_functional (ha.max hb),toPotential_functional (ha.min hb)]
  have hh := cosineSeries_logPartition_supermodular a b id ha.nonneg hb.nonneg ha.summable hb.summable
  have he := congrArg (fun x : ℝ => A*x) (energy_lattice ha hb)
  simp only [mul_add] at he
  linarith only [hh,he]

/-- If both original potentials maximize, their actual coefficientwise
maximum and minimum are admissible maximizers with the same value. -/
theorem lattice_maximizers {d : ℕ} {a b : Frequency d → ℝ}
    (ha : Domain a) (hb : Domain b) (A M : ℝ)
    (hglobal : ∀ v : TorusL2 d,Admissible v → functional A v≤M)
    (haM : functional A (toPotential a)=M) (hbM : functional A (toPotential b)=M) :
    functional A (toPotential (fun k => max (a k) (b k)))=M ∧
      functional A (toPotential (fun k => min (a k) (b k)))=M := by
  have hs := functional_supermodular ha hb A
  have hmax := hglobal _ (toPotential_admissible (ha.max hb))
  have hmin := hglobal _ (toPotential_admissible (ha.min hb))
  rw [haM,hbM] at hs
  constructor <;> linarith

#print axioms series_coefficient
#print axioms toPotential_admissible
#print axioms functional_supermodular
#print axioms lattice_maximizers
end BecknerOnofri.HighDim.CosineCoefficientLattice
