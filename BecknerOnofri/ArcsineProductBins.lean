module

public import BecknerOnofri.ArcsineCircle
public import BecknerOnofri.Definitions
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Exact multidimensional sine-square bins and their product probabilities.
These are statements about the genuine Haar torus, before numerical enclosure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.ArcsineProductBins
open ArcsineCircle

def radialSum {d : ℕ} (x : Torus d) : ℝ := ∑ i,sineSquare (x i)

def cell {N d : ℕ} (b : Fin d → Fin N) : Set (Torus d) :=
  Set.pi Set.univ (fun i => bin N (b i).val)

def indexSum {N d : ℕ} (b : Fin d → Fin N) : ℕ := ∑ i,(b i).val

def cellMass {N d : ℕ} (b : Fin d → Fin N) : ℝ := ∏ i,binMass N (b i).val

theorem radialSum_continuous (d : ℕ) : Continuous (@radialSum d) := by
  apply continuous_finset_sum
  intro i _
  exact sineSquare_continuous.comp (continuous_apply i)

theorem radialSum_mem {d : ℕ} (x : Torus d) : radialSum x∈Icc (0:ℝ) d := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (sineSquare_mem (x i)).1)
  · calc
      _ ≤ ∑ _i : Fin d,(1:ℝ) := Finset.sum_le_sum (fun i _ => (sineSquare_mem (x i)).2)
      _ = _ := by simp

theorem radialSum_coe {d : ℕ} (x : Fin d → ℝ) :
    radialSum (fun i => (x i : UnitAddCircle))=∑ i,Real.sin (Real.pi*x i)^2 := by
  simp only [radialSum,sineSquare_coe]

theorem cell_measurable {N d : ℕ} (b : Fin d → Fin N) : MeasurableSet (cell b) :=
  MeasurableSet.univ_pi (fun i => bin_measurable N (b i).val)

theorem cell_measure {N d : ℕ} (hN : 0<N) (b : Fin d → Fin N) :
    (torusMeasure d).real (cell b)=cellMass b := by
  rw [measureReal_def,torusMeasure,cell,Measure.pi_pi,ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => bin_measure hN (b i).isLt)

theorem cellMass_nonneg {N d : ℕ} (hN : 0<N) (b : Fin d → Fin N) : 0≤cellMass b := by
  rw [← cell_measure hN b]
  exact measureReal_nonneg

theorem cells_disjoint {N d : ℕ} (hN : 0<N) {a b : Fin d → Fin N} (hab : a≠b) :
    Disjoint (cell a) (cell b) := by
  obtain ⟨i,hi⟩ : ∃ i,a i≠b i := Function.ne_iff.mp hab
  have hij : (a i).val≠(b i).val := fun h => hi (Fin.ext h)
  rw [Set.disjoint_left]
  intro x hx hy
  exact Set.disjoint_left.mp (bins_disjoint hN hij) (hx i (Set.mem_univ i)) (hy i (Set.mem_univ i))

/-- Every cell has the exact half-open sum interval used by the manuscript. -/
theorem cell_location {N d : ℕ} (hN : 0<N) (hd : 0<d) {b : Fin d → Fin N}
    {x : Torus d} (hx : x∈cell b) :
    (indexSum b:ℝ)/N≤radialSum x ∧ radialSum x<((indexSum b:ℝ)+d)/N := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hl : (∑ i : Fin d,((b i).val:ℝ))≤∑ i : Fin d,sineSquare (x i)*N := by
    apply Finset.sum_le_sum
    intro i _
    exact (div_le_iff₀ hNr).mp (hx i (Set.mem_univ i)).1
  have hu : (∑ i : Fin d,sineSquare (x i)*N)<∑ i : Fin d,(((b i).val:ℝ)+1) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact ((lt_div_iff₀ hNr).mp (hx i (Set.mem_univ i)).2).le
    · exact ⟨⟨0,hd⟩,Finset.mem_univ _,(lt_div_iff₀ hNr).mp (hx ⟨0,hd⟩ (Set.mem_univ _)).2⟩
  simp only [← Finset.sum_mul,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one] at hl hu
  constructor
  · apply (div_le_iff₀ hNr).mpr
    simpa [indexSum,radialSum] using hl
  · apply (lt_div_iff₀ hNr).mpr
    simpa [indexSum,radialSum] using hu

theorem cell_crossing_index {N d : ℕ} (hN : 0<N) (hd : 0<d) (hdN : d≤N)
    {b : Fin d → Fin N} {x : Torus d} (hx : x∈cell b) (hS : 1<radialSum x) :
    N-d+1 ≤ indexSum b := by
  have hu := (cell_location hN hd hx).2
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have h : (N:ℝ)<(indexSum b:ℝ)+d := by
    simpa only [mul_one] using (lt_div_iff₀' hNr).mp (hS.trans hu)
  have hnat : N < indexSum b+d := by exact_mod_cast h
  omega

/-- The only excluded coordinate endpoint has Haar measure zero. -/
theorem cells_cover_ae {N d : ℕ} (hN : 0<N) :
    ∀ᵐ x ∂torusMeasure d, ∃ b : Fin d → Fin N,x∈cell b := by
  have hi (i : Fin d) : ∀ᵐ x ∂torusMeasure d,sineSquare (x i)<1 :=
    (measurePreserving_eval (fun _ : Fin d => AddCircle.haarAddCircle (T:=1)) i).quasiMeasurePreserving.ae
      sineSquare_lt_one_ae
  filter_upwards [ae_all_iff.mpr hi] with x hx
  choose b hb using fun i => exists_bin hN (x i) (hx i)
  exact ⟨b,fun i _ => hb i⟩

#print axioms cell_measure
#print axioms cell_location
#print axioms cell_crossing_index
#print axioms cells_cover_ae
end BecknerOnofri.HighDim.ArcsineProductBins
