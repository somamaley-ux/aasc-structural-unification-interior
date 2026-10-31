import OriginalEHJointConnection
import OriginalEHRicciConnection

/-! Variation of the actual connection Ricci contraction. Spatial/variation
interchange is supplied by a proved actual mixed derivative, not a receipt. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

def ehConnectionRicciVariation (g h : MetricField) (p : CoordinatePoint) (a b : Fin 4) : ℝ :=
  ∑ j : Fin 4,
    (scalarPartial (fun x => ehLCVariation g h x j b a) p j -
      scalarPartial (fun x => ehLCVariation g h x j j a) p b +
      (∑ e : Fin 4, (ehLCVariation g h p j j e * leviCivitaCoefficients g p e b a +
        leviCivitaCoefficients g p j j e * ehLCVariation g h p e b a)) -
      (∑ e : Fin 4, (ehLCVariation g h p j b e * leviCivitaCoefficients g p e j a +
        leviCivitaCoefficients g p j b e * ehLCVariation g h p e j a)))

theorem eh_connection_ricci_actual_variation (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b : Fin 4) :
    HasDerivAt (fun t : ℝ => ehConnectionRicci
      (leviCivitaCoefficients (ehMetricRay g h t)) p a b)
      (ehConnectionRicciVariation g h p a b) 0 := by
  have lc (i j k : Fin 4) := eh_levi_civita_variation g h p
    (eh_smooth_metric_c2_at g hg p) (eh_smooth_metric_c2_at h hh p) hn i j k
  have first (i j k r : Fin 4) := eh_lc_actual_mixed_variation g h hg hh p hn i j k r
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (((first j b a j).sub (first j j a b)).add
      (HasDerivAt.fun_sum (u := Finset.univ) (fun e _ =>
        (lc j j e).mul (lc e b a)))).sub
      (HasDerivAt.fun_sum (u := Finset.univ) (fun e _ =>
        (lc j b e).mul (lc e j a))))
  simpa only [ehConnectionRicci,connectionCurvature,scalarPartial,
    ehConnectionRicciVariation,eh_metric_ray_zero] using hd

theorem eh_ricci_variation_is_palatini (g h : MetricField)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b : Fin 4) :
    ehRicciVariation g h p a b = ehConnectionRicciVariation g h p a b := by
  have hd := eh_connection_ricci_actual_variation g h hg hh p hn a b
  have actual : HasDerivAt (fun t : ℝ => coordinateRicci (ehMetricRay g h t) p a b)
      (ehConnectionRicciVariation g h p a b) 0 := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [eh_metric_ray_nondegenerate_near g h p hn] with t ht
    exact eh_actual_ricci_is_connection_ricci (ehMetricRay g h t)
      (eh_metric_ray_symmetric g h sg sh t) p ht a b
  exact (eh_ricci_variation g h p sg sh (eh_smooth_metric_c2_at g hg p)
    (eh_smooth_metric_c2_at h hh p) hn a b).unique actual

theorem eh_lc_variation_lower_symmetric (g h : MetricField)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (p : CoordinatePoint) (a b c : Fin 4) :
    ehLCVariation g h p a b c = ehLCVariation g h p a c b := by
  simp only [ehLCVariation,lowerChristoffel_torsion_free g sg p _ b c,
    lowerChristoffel_torsion_free h sh p _ b c]

end
end AASCSemanticExhaustion
