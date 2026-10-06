module

public import BecknerOnofri.Friedrichs.SpatialOperatorProperties

@[expose] public section

/-! The concrete Jacobi eigenvectors belong to the independently defined spatial
operator graph, with their actual differential eigenvalues. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm
open Legacy.BecknerOnofri.JacobiAngular
open Legacy.BecknerOnofri.JacobiEigenfunctions (polynomial eigenfunction eigenvector eigenvalue
  eigenvector_ae_eq eigenfunction_equation)

lemma angularImageLp_eigenvector (m n : ℕ) :
    angularImageLp m (polynomial_contDiff (polynomial m n))=eigenvalue m n • eigenvector m n := by
  apply Lp.ext
  filter_upwards [(continuous_memLp (angularImage_continuous m
    (polynomial_contDiff (polynomial m n)))).coeFn_toLp,
    Lp.coeFn_smul (eigenvalue m n) (eigenvector m n),eigenvector_ae_eq m n,
    ae_restrict_mem measurableSet_Ioo] with t ht hs he hi
  change angularImageLp m (polynomial_contDiff (polynomial m n)) t=angularImage m (fun x => (polynomial m n).eval x) t at ht
  rw [ht,hs]
  simp only [Pi.smul_apply,smul_eq_mul,he]
  have hc := angular_conjugation m (polynomial_contDiff (polynomial m n))
    (Real.sin_pos_of_pos_of_lt_pi hi.1 hi.2).ne'
  have heq := eigenfunction_equation m n hi
  change angularOperator m (eigenfunction m n) t=angularImage m (fun x => (polynomial m n).eval x) t at hc
  exact hc.symm.trans heq

theorem eigenvector_operatorGraph {m : ℕ} (hm : 0<m) (n : ℕ) :
    operatorGraph m (eigenvector m n) (eigenvalue m n • eigenvector m n) := by
  have h := angular_operatorGraph hm (polynomial_contDiff (polynomial m n))
  rwa [angularLift_eigenvector hm n,angularImageLp_eigenvector m n] at h

theorem operatorGraph_spectral_coefficients {m : ℕ} (hm : 0<m) {f g : H}
    (h : operatorGraph m f g) (n : ℕ) :
    inner ℝ g (eigenvector m n)=eigenvalue m n*inner ℝ f (eigenvector m n) := by
  have he := operatorGraph_symmetric h (eigenvector_operatorGraph hm n)
  simpa only [inner_smul_right] using he

#print axioms eigenvector_operatorGraph
#print axioms operatorGraph_spectral_coefficients
end BecknerOnofri.Friedrichs.SpatialForm
