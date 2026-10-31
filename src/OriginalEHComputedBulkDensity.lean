import OriginalEHRicciSymmetry
import NativeRegularDensityLF

/-! Regularity of the coefficient computed by the density decomposition.
This coefficient is a representation witness; the Euler response will be
constructed from the original action's unique first-variation functional. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory TopologicalSpace
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

def ehComputedBulkDensity (κ Λ : ℝ) (g : MetricField) (p : CoordinatePoint) : Tensor2 :=
  -(coordinateVolumeDensity g p / (2*κ)) •
    ((g p)⁻¹ * (coordinateRicci g p -
      (coordinateScalarCurvature g p / 2) • g p + Λ • g p) * (g p)⁻¹)

def ehComputedSourceDensity (κ Λ : ℝ) (g : MetricField)
    (i : Fin 10) (p : CoordinatePoint) : ℝ :=
  2 * tensorDecode (ehComputedBulkDensity κ Λ g p) i

theorem eh_actual_connection_smooth_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b c : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => leviCivitaCoefficients g x a b c) p :=
  (eh_jet_lc_smooth_at (ehActualMetricJet g p) hn a b c).comp p
    (eh_actual_metric_jet_contDiff g hg).contDiffAt

theorem eh_actual_connection_curvature_smooth_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b c d : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => connectionCurvature (leviCivitaCoefficients g) x a b c d) p := by
  have hc (i j k : Fin 4) := eh_actual_connection_smooth_at g hg p hn i j k
  have hd (i j k r : Fin 4) : ContDiffAt ℝ ∞
      (fun x => scalarPartial (fun y => leviCivitaCoefficients g y i j k) x r) p :=
    ((hc i j k).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  exact (((hd a d b c).sub (hd a c b d)).add
    (ContDiffAt.sum (fun e _ => (hc a c e).mul (hc e d b)))).sub
      (ContDiffAt.sum (fun e _ => (hc a d e).mul (hc e c b)))

theorem eh_actual_lowered_curvature_smooth_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b c d : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => loweredConnectionCurvature g
      (leviCivitaCoefficients g) x a b c d) p := by
  unfold loweredConnectionCurvature
  exact ContDiffAt.sum (fun e _ => (hg a e).contDiffAt.mul
    (eh_actual_connection_curvature_smooth_at g hg p hn e b c d))

theorem eh_actual_ricci_smooth_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => coordinateRicci g x a b) p := by
  unfold coordinateRicci
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
    (eh_inverse_component_smooth_at g hg p hn i j).mul
      (eh_actual_lowered_curvature_smooth_at g hg p hn i a j b)))

theorem eh_actual_scalar_curvature_smooth_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) : ContDiffAt ℝ ∞ (coordinateScalarCurvature g) p := by
  unfold coordinateScalarCurvature
  exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
    (eh_inverse_component_smooth_at g hg p hn a b).mul
      (eh_actual_ricci_smooth_at g hg p hn a b)))

theorem eh_computed_bulk_density_smooth_at (κ Λ : ℝ) (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (negative : (g p).det < 0) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => ehComputedBulkDensity κ Λ g x a b) p := by
  have hi (i j : Fin 4) := eh_inverse_component_smooth_at g hg p (ne_of_lt negative) i j
  have hr (i j : Fin 4) := eh_actual_ricci_smooth_at g hg p (ne_of_lt negative) i j
  have hs := eh_actual_scalar_curvature_smooth_at g hg p (ne_of_lt negative)
  have he (i j : Fin 4) : ContDiffAt ℝ ∞ (fun x =>
      (coordinateRicci g x - (coordinateScalarCurvature g x / 2) • g x + Λ • g x) i j) p :=
    ((hr i j).sub ((hs.div_const 2).mul (hg i j).contDiffAt)).add
      (contDiffAt_const.mul (hg i j).contDiffAt)
  have inner (i j : Fin 4) : ContDiffAt ℝ ∞ (fun x =>
      ((g x)⁻¹ * (coordinateRicci g x -
        (coordinateScalarCurvature g x / 2) • g x + Λ • g x)) i j) p := by
    simp only [Matrix.mul_apply]
    exact ContDiffAt.sum (fun k _ => (hi i k).mul (he k j))
  have raised : ContDiffAt ℝ ∞ (fun x =>
      ((g x)⁻¹ * (coordinateRicci g x -
        (coordinateScalarCurvature g x / 2) • g x + Λ • g x) * (g x)⁻¹) a b) p := by
    change ContDiffAt ℝ ∞ (fun x => ∑ k : Fin 4,
      ((g x)⁻¹ * (coordinateRicci g x -
        (coordinateScalarCurvature g x / 2) • g x + Λ • g x)) a k * (g x)⁻¹ k b) p
    exact ContDiffAt.sum (fun k _ => (inner a k).mul (hi k b))
  exact ((eh_volume_density_smooth_at g hg p negative).div_const (2*κ)).neg.mul raised

theorem eh_computed_bulk_density_symmetric (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (a b : Fin 4) :
    ehComputedBulkDensity κ Λ g p a b = ehComputedBulkDensity κ Λ g p b a := by
  by_cases negative : (g p).det < 0
  · exact congrArg (fun r : ℝ => -(coordinateVolumeDensity g p / (2*κ)) * r)
      (eh_einstein_raised_matrix_symmetric g sg hg p (ne_of_lt negative) Λ a b)
  · have hv : coordinateVolumeDensity g p = 0 :=
      Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr (le_of_not_gt negative))
    simp only [ehComputedBulkDensity,hv,zero_div,neg_zero,zero_smul,Matrix.zero_apply]

theorem eh_computed_source_density_smooth_at (κ Λ : ℝ) (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (negative : (g p).det < 0) (i : Fin 10) :
    ContDiffAt ℝ ∞ (ehComputedSourceDensity κ Λ g i) p := by
  fin_cases i <;> exact contDiffAt_const.mul
    (eh_computed_bulk_density_smooth_at κ Λ g hg p negative _ _)

theorem eh_computed_source_density_locally_integrable {Ω : Opens CoordinatePoint}
    (κ Λ : ℝ) (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (i : Fin 10) :
    LocallyIntegrableOn (ehComputedSourceDensity κ Λ g i) (Ω : Set CoordinatePoint) volume := by
  apply ContinuousOn.locallyIntegrableOn _ Ω.isOpen.measurableSet
  intro p hp
  exact (eh_computed_source_density_smooth_at κ Λ g hg p (negative p hp) i).continuousAt.continuousWithinAt

end
end AASCSemanticExhaustion
