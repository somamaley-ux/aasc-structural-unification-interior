import OriginalEHLorentzNeighborhood

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCKleinGordon MeasureTheory Filter Set TopologicalSpace
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem eh_compact_lorentz_ray_near {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (G H : X → Tensor2) (hG : Continuous G) (hH : Continuous H)
    (sG : ∀ x i j, G x i j = G x j i) (sH : ∀ x i j, H x i j = H x j i)
    (frames : ∀ x, ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint,
      (coordinateFrameMatrix B).transpose * G x * coordinateFrameMatrix B = metric) :
    ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧ ∀ t ∈ U, ∀ x,
      ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint,
        (coordinateFrameMatrix B).transpose * (G x + t • H x) * coordinateFrameMatrix B = metric := by
  let A : ℝ × X → Tensor2 := fun z => G z.2 + z.1 • H z.2
  have continuousA : Continuous A := (hG.comp continuous_snd).add
    (continuous_fst.smul (hH.comp continuous_snd))
  let D : Set (ℝ × X) := A ⁻¹' ehLorentzNeighborhood
  have openD : IsOpen D := eh_lorentz_neighborhood_open.preimage continuousA
  have base : ({0} : Set ℝ) ×ˢ (univ : Set X) ⊆ D := by
    rintro ⟨t,x⟩ ⟨ht,_⟩
    have ht0 : t = 0 := ht
    subst t
    obtain ⟨B,frame⟩ := frames x
    simpa [D,A] using eh_frame_in_lorentz_neighborhood (G x) B frame
  obtain ⟨U,V,hU,_,hzero,hall,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) isCompact_univ openD base
  refine ⟨U,hU,hzero (by simp),?_⟩
  intro t ht x
  apply eh_symmetric_lorentz_neighborhood_has_frame
  · intro i j
    change G x i j + t * H x i j = G x j i + t * H x j i
    rw [sG x i j,sH x i j]
  · exact hUV (show (t,x) ∈ U ×ˢ V from ⟨ht,hall (mem_univ x)⟩)

variable {Ω : Opens CoordinatePoint}

theorem eh_original_small_ray_lorentz (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (frames : ∀ p ∈ Ω, ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint, LorentzFrameAt g p B)
    (h : MetricSourceProbe Ω) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ p ∈ Ω, C2LorentzMetricAt (originalEHMetricPerturbation g (t • h)) p := by
  let K : Set CoordinatePoint := tsupport h
  letI : CompactSpace K := isCompact_iff_compactSpace.mp h.hasCompactSupport
  have smoothG : ContDiff ℝ ∞ g := contDiff_pi.mpr (fun a => contDiff_pi.mpr (hg a))
  have smoothH : ContDiff ℝ ∞ (ehProbeMetric h) :=
    contDiff_pi.mpr (fun a => contDiff_pi.mpr (eh_probe_metric_smooth h a))
  obtain ⟨U,hU,hzero,near⟩ := eh_compact_lorentz_ray_near
    (fun p : K => g p) (fun p : K => ehProbeMetric h p)
    (smoothG.continuous.comp continuous_subtype_val) (smoothH.continuous.comp continuous_subtype_val)
    (fun p => sg p) (fun p => eh_probe_metric_symmetric h p)
    (fun p => frames p (h.tsupport_subset p.property))
  filter_upwards [hU.mem_nhds hzero] with t ht
  intro p hp
  rw [eh_perturbed_probe_is_ray]
  refine ⟨eh_metric_ray_symmetric g (ehProbeMetric h) sg (eh_probe_metric_symmetric h) t,?_,?_⟩
  · intro a b
    exact ((hg a b).add (contDiff_const.mul (eh_probe_metric_smooth h a b))).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  · by_cases inside : p ∈ K
    · exact near t ht ⟨p,inside⟩
    · obtain ⟨B,frame⟩ := frames p hp
      refine ⟨B,?_⟩
      have zero : ehProbeMetric h p = (0 : Tensor2) :=
        (eh_probe_metric_zero_near_outside_support h p inside).eq_of_nhds
      change (coordinateFrameMatrix B).transpose * ehMetricRay g (ehProbeMetric h) t p *
        coordinateFrameMatrix B = metric
      rw [eh_metric_ray_value,zero,smul_zero,add_zero]
      exact frame

theorem eh_original_relative_integrand_ray (κ Λ : ℝ) (g : MetricField)
    (h : MetricSourceProbe Ω) (t : ℝ) :
    originalEHRelativeIntegrand κ Λ g (t • h) = fun p =>
      originalEHScalarDensity κ Λ (ehMetricRay g (ehProbeMetric h) t) p -
        originalEHScalarDensity κ Λ g p := by
  unfold originalEHRelativeIntegrand
  rw [eh_perturbed_probe_is_ray]

theorem eh_original_density_continuousAt (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) :
    ContinuousAt (originalEHScalarDensity κ Λ g) p := by
  have reg (x : CoordinatePoint) : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) x :=
    fun a b => (hg a b).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have smoothG : ContDiff ℝ ∞ g := contDiff_pi.mpr (fun a => contDiff_pi.mpr (hg a))
  have near : ∀ᶠ x in 𝓝 p, (g x).det < 0 :=
    smoothG.continuous.matrix_det.continuousAt.eventually
      (eventually_lt_nhds negative)
  have jet := eh_actual_metric_jet_contDiff g hg
  have computed := (eh_jet_density_contDiffAt κ Λ (ehActualMetricJet g p) negative).continuousAt.comp
    jet.continuous.continuousAt
  apply computed.congr_of_eventuallyEq
  filter_upwards [near] with x hx
  exact (eh_jet_density_is_actual κ Λ g x sg (reg x) (ne_of_lt hx)).symm

theorem eh_original_admitted_relative_integrable (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) (t : ℝ)
    (target : ∀ p ∈ Ω, C2LorentzMetricAt (originalEHMetricPerturbation g (t • h)) p) :
    IntegrableOn (originalEHRelativeIntegrand κ Λ g (t • h)) (Ω : Set CoordinatePoint) := by
  rw [eh_original_relative_integrand_ray]
  let H := ehProbeMetric h
  have raySmooth : ∀ a b, ContDiff ℝ ∞ (fun x => ehMetricRay g H t x a b) :=
    fun a b => (hg a b).add (contDiff_const.mul (eh_probe_metric_smooth h a b))
  have raySym := eh_metric_ray_symmetric g H sg (eh_probe_metric_symmetric h) t
  have targetNegative (p : CoordinatePoint) (hp : p ∈ Ω) :
      (ehMetricRay g H t p).det < 0 := by
    obtain ⟨B,frame⟩ := (target p hp).2.2
    rw [eh_perturbed_probe_is_ray] at frame
    exact native_lorentz_frame_determinant_negative _ p B frame
  have hc : ContinuousOn (fun p => originalEHScalarDensity κ Λ (ehMetricRay g H t) p -
      originalEHScalarDensity κ Λ g p) (tsupport h) := by
    intro p hp
    have inside := h.tsupport_subset hp
    have first := eh_original_density_continuousAt κ Λ (ehMetricRay g H t) raySym raySmooth p
      (targetNegative p inside)
    have second := eh_original_density_continuousAt κ Λ g sg hg p (negative p inside)
    exact (first.sub second).continuousWithinAt
  have intK := hc.integrableOn_compact (μ := volume) h.hasCompactSupport
  have support : Function.support (fun p => originalEHScalarDensity κ Λ (ehMetricRay g H t) p -
      originalEHScalarDensity κ Λ g p) ⊆ tsupport h := by
    intro p hp
    by_contra outside
    apply hp
    exact eh_relative_density_zero_outside_support κ Λ g h p outside t
  exact ((integrableOn_iff_integrable_of_support_subset support).mp intK).integrableOn

theorem eh_original_small_ray_finite_use_domain (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (frames : ∀ p ∈ Ω, ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint, LorentzFrameAt g p B)
    (h : MetricSourceProbe Ω) :
    ∀ᶠ t : ℝ in 𝓝 0, OriginalEHFiniteUseDomain κ Λ g (t • h) := by
  have base : ∀ p ∈ Ω, C2LorentzMetricAt g p := by
    intro p hp
    refine ⟨sg,?_,frames p hp⟩
    exact fun a b => (hg a b).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have negative : ∀ p ∈ Ω, (g p).det < 0 := by
    intro p hp
    obtain ⟨B,frame⟩ := frames p hp
    exact native_lorentz_frame_determinant_negative g p B frame
  filter_upwards [eh_original_small_ray_lorentz g sg hg frames h] with t ht
  exact ⟨hk,base,ht,eh_original_admitted_relative_integrable κ Λ g sg hg negative h t ht⟩

theorem eh_original_small_ray_evaluation_success (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (frames : ∀ p ∈ Ω, ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint, LorentzFrameAt g p B)
    (h : MetricSourceProbe Ω) :
    ∀ᶠ t : ℝ in 𝓝 0, (originalEHFiniteUse κ Λ g (t • h)).2 =
      some (originalEHRelativeAction κ Λ g (t • h)) := by
  filter_upwards [eh_original_small_ray_finite_use_domain κ Λ hk g sg hg frames h] with t ht
  exact (original_eh_finite_use_success_exact κ Λ g (t • h) _).mpr ⟨ht,rfl⟩

end
end AASCSemanticExhaustion
