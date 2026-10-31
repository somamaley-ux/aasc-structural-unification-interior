import OriginalEHMixedCalculus

/-! Joint smoothness of the actual connection along the same metric ray,
and its actual mixed spatial/parameter derivative. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

theorem eh_smooth_metric_c2_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint) :
    ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p := fun a b =>
  (hg a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem eh_joint_metric_jet_smooth (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) :
    ContDiff ℝ ∞ (fun z : EHJointPoint => ehActualMetricJet (ehMetricRay g h z.1) z.2) := by
  have he : (fun z : EHJointPoint => ehActualMetricJet (ehMetricRay g h z.1) z.2) =
      fun z => ehActualMetricJet g z.2 + z.1 • ehActualMetricJet h z.2 := by
    funext z
    exact eh_actual_metric_jet_ray g h z.2 (eh_smooth_metric_c2_at g hg z.2)
      (eh_smooth_metric_c2_at h hh z.2) z.1
  rw [he]
  exact ((eh_actual_metric_jet_contDiff g hg).comp contDiff_snd).add
    (contDiff_fst.smul ((eh_actual_metric_jet_contDiff h hh).comp contDiff_snd))

theorem eh_jet_lc_smooth_at (J : EHMetricJet) (hn : J.1.det ≠ 0) (a b c : Fin 4) :
    ContDiffAt ℝ ∞ (fun K : EHMetricJet => ehJetLC K a b c) J := by
  have first (i j k : Fin 4) : ContDiffAt ℝ ∞ (fun K : EHMetricJet => K.2.1 i j k) J :=
    (ehJetFirstEntry i j k).contDiff.contDiffAt
  unfold ehJetLC
  apply ContDiffAt.sum
  intro d _
  apply ((eh_jet_inverse_entry_contDiffAt J hn a d).of_le
    (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).mul
  exact contDiffAt_const.mul (((first d c b).add (first d b c)).sub (first b c d))

theorem eh_joint_connection_smooth_at (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b c : Fin 4) :
    ContDiffAt ℝ 2 (fun z : EHJointPoint =>
      leviCivitaCoefficients (ehMetricRay g h z.1) z.2 a b c) (0,p) := by
  have hj := (eh_joint_metric_jet_smooth g h hg hh).contDiffAt (x := (0,p))
  have hv : ehActualMetricJet (ehMetricRay g h 0) p = ehActualMetricJet g p := by
    rw [eh_metric_ray_zero]
  have ho : ContDiffAt ℝ ∞ (fun K : EHMetricJet => ehJetLC K a b c)
      (ehActualMetricJet (ehMetricRay g h 0) p) := by
    rw [hv]
    exact eh_jet_lc_smooth_at _ hn a b c
  exact (ho.comp (0,p) hj).of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem eh_lc_actual_mixed_variation (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b c r : Fin 4) :
    HasDerivAt (fun t : ℝ => scalarPartial
      (fun x => leviCivitaCoefficients (ehMetricRay g h t) x a b c) p r)
      (scalarPartial (fun x => ehLCVariation g h x a b c) p r) 0 := by
  apply eh_actual_mixed_partial
    (fun z : EHJointPoint => leviCivitaCoefficients (ehMetricRay g h z.1) z.2 a b c)
    (fun x => ehLCVariation g h x a b c) p
    (eh_joint_connection_smooth_at g h hg hh p hn a b c) _ r
  filter_upwards [c2_metric_nondegenerate_eventually g p
    (eh_smooth_metric_c2_at g hg p) hn] with q hq
  exact (eh_levi_civita_variation g h q (eh_smooth_metric_c2_at g hg q)
    (eh_smooth_metric_c2_at h hh q) hq a b c).deriv.symm

end
end AASCSemanticExhaustion
