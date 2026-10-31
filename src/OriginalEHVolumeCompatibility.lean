import OriginalEHJointConnection
import OriginalEHCompactBoundaryIBP

/-! Actual inverse compatibility and spatial volume differentiation.
Both identities are derived from the constructed metric connection/calculus. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

def ehConnectionMatrix (g : MetricField) (p : CoordinatePoint) (c : Fin 4) : Tensor2 :=
  fun a b => leviCivitaCoefficients g p a c b

theorem eh_inverse_symmetric (g : MetricField) (sg : MetricFieldSymmetric g)
    (p : CoordinatePoint) (a b : Fin 4) : (g p)⁻¹ a b = (g p)⁻¹ b a := by
  have hs : (g p).transpose = g p := by
    ext i j
    exact sg p j i
  have hb : ((g p)⁻¹).transpose = (g p)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv,hs]
  exact congrArg (fun M : Tensor2 => M b a) hb

theorem eh_metric_partial_connection_matrix (g : MetricField) (sg : MetricFieldSymmetric g)
    (p : CoordinatePoint) (hn : (g p).det ≠ 0) (c : Fin 4) :
    ehMatrixPartial g p c =
      (ehConnectionMatrix g p c).transpose * g p + g p * ehConnectionMatrix g p c := by
  ext a b
  change metricPartial g p a b c = _
  rw [leviCivita_metric_compatible g sg p hn a b c]
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,ehConnectionMatrix]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem eh_inverse_partial_connection_matrix (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (hn : (g p).det ≠ 0) (c : Fin 4) :
    ehMatrixPartial (fun x => (g x)⁻¹) p c =
      -(ehConnectionMatrix g p c * (g p)⁻¹ +
        (g p)⁻¹ * (ehConnectionMatrix g p c).transpose) := by
  rw [eh_inverse_spatial_derivative g hg p hn c,
    eh_metric_partial_connection_matrix g sg p hn c]
  have hi : g p * (g p)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn)
  have hj : (g p)⁻¹ * g p = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hn)
  simp only [neg_mul,mul_add,add_mul,Matrix.mul_assoc,hi,mul_one]
  rw [← Matrix.mul_assoc (g p)⁻¹ (g p),hj,one_mul]
  abel

theorem eh_inverse_partial_compatible (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (hn : (g p).det ≠ 0) (a b c : Fin 4) :
    scalarPartial (fun x => (g x)⁻¹ a b) p c =
      -(∑ d : Fin 4, leviCivitaCoefficients g p a c d * (g p)⁻¹ d b) -
        (∑ d : Fin 4, leviCivitaCoefficients g p b c d * (g p)⁻¹ a d) := by
  have hi := congrArg (fun M : Tensor2 => M a b)
    (eh_inverse_partial_connection_matrix g sg hg p hn c)
  simpa only [ehMatrixPartial,ehConnectionMatrix,Matrix.neg_apply,Matrix.add_apply,
    Matrix.mul_apply,Matrix.transpose_apply,neg_add_rev,mul_comm,sub_eq_add_neg,add_comm] using hi

theorem eh_matrix_volume_differentiableAt (G : Tensor2) (negative : G.det < 0) :
    DifferentiableAt ℝ (fun M : Tensor2 => Real.sqrt (-M.det)) G := by
  have det : ContDiff ℝ ∞ (fun M : Tensor2 => M.det) := by
    simp only [Matrix.det_apply']
    apply ContDiff.sum
    intro σ _
    apply contDiff_const.mul
    apply contDiff_prod
    intro j _
    exact (nativeRealMatrixEntry (σ j) j).contDiff
  exact (det.contDiffAt.neg.sqrt (neg_ne_zero.mpr (ne_of_lt negative))).differentiableAt
    (by norm_num)

theorem eh_volume_spatial_trace (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) (c : Fin 4) :
    scalarPartial (coordinateVolumeDensity g) p c =
      (1/2 : ℝ) * coordinateVolumeDensity g p * Matrix.trace ((g p)⁻¹ * ehMatrixPartial g p c) := by
  let V : Tensor2 → ℝ := fun M => Real.sqrt (-M.det)
  let e : CoordinatePoint := Pi.single c 1
  have hp : HasDerivAt (fun t : ℝ => p + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p
  have hgpath : HasDerivAt (fun t : ℝ => g (p+t • e)) (ehMatrixPartial g p c) 0 := by
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    have outer : HasFDerivAt (fun x => g x a b)
        (fderiv ℝ (fun x => g x a b) p) (p + (0 : ℝ) • e) := by
      simpa only [zero_smul,add_zero] using ((hg a b).differentiable (by norm_num) p).hasFDerivAt
    have hd := outer.comp_hasDerivAt 0 hp
    simpa only [zero_smul,add_zero,Function.comp_def,ehMatrixPartial,scalarPartial,e] using hd
  have hv := (eh_matrix_volume_differentiableAt (g p) negative).hasFDerivAt
  have hvalue : fderiv ℝ V (g p) (ehMatrixPartial g p c) =
      (1/2 : ℝ) * V (g p) * Matrix.trace ((g p)⁻¹ * ehMatrixPartial g p c) := by
    have hr : HasDerivAt (fun t : ℝ => g p + t • ehMatrixPartial g p c)
        (ehMatrixPartial g p c) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ehMatrixPartial g p c)).const_add (g p)
    have outer : HasFDerivAt V (fderiv ℝ V (g p))
        (g p + (0 : ℝ) • ehMatrixPartial g p c) := by
      simpa only [zero_smul,add_zero] using hv
    have hd := outer.comp_hasDerivAt 0 hr
    exact hd.unique (original_eh_lorentz_volume_variation (g p) (ehMatrixPartial g p c) negative)
  have outer : HasFDerivAt V (fderiv ℝ V (g p)) (g (p + (0 : ℝ) • e)) := by
    simpa only [zero_smul,add_zero] using hv
  have actual := outer.comp_hasDerivAt 0 hgpath
  have source : HasFDerivAt (coordinateVolumeDensity g)
      (fderiv ℝ (coordinateVolumeDensity g) p) (p + (0 : ℝ) • e) := by
    simpa only [zero_smul,add_zero] using
      ((eh_volume_density_smooth_at g hg p negative).differentiableAt (by norm_num)).hasFDerivAt
  have spatial := source.comp_hasDerivAt 0 hp
  exact (spatial.unique actual).trans hvalue

theorem eh_volume_partial_connection_trace (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) (c : Fin 4) :
    scalarPartial (coordinateVolumeDensity g) p c =
      coordinateVolumeDensity g p * (∑ a : Fin 4, leviCivitaCoefficients g p a c a) := by
  rw [eh_volume_spatial_trace g hg p negative c,
    eh_metric_partial_connection_matrix g sg p (ne_of_lt negative) c]
  have hi : g p * (g p)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_lt negative))
  have hj : (g p)⁻¹ * g p = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_lt negative))
  rw [mul_add,Matrix.trace_add,← Matrix.mul_assoc,
    Matrix.trace_mul_cycle (g p)⁻¹ (ehConnectionMatrix g p c).transpose (g p),hi,
    one_mul,Matrix.trace_transpose,← Matrix.mul_assoc,hj,one_mul]
  change (1/2 : ℝ) * coordinateVolumeDensity g p *
    ((∑ a : Fin 4, leviCivitaCoefficients g p a c a) +
      (∑ a : Fin 4, leviCivitaCoefficients g p a c a)) = _
  ring

end
end AASCSemanticExhaustion
