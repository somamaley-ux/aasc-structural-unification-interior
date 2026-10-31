import OriginalEHCompactVariation

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter TopologicalSpace Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem eh_actual_jet_congr_of_eventuallyEq (g k : MetricField) (p : CoordinatePoint)
    (same : g =ᶠ[𝓝 p] k) : ehActualMetricJet g p = ehActualMetricJet k p := by
  have hj := metric_twojet_of_eventuallyEq g k p same
  apply Prod.ext hj.1
  apply Prod.ext
  · funext a b c
    exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single c 1)) (hj.2.1 a b)
  · funext a b c d
    exact hj.2.2 a b c d

/-- Local equality suffices even outside the nondegenerate branch: the total
raw definitions use only local values and derivatives. -/
theorem eh_density_congr_of_eventuallyEq (κ Λ : ℝ) (g k : MetricField) (p : CoordinatePoint)
    (same : g =ᶠ[𝓝 p] k) : originalEHScalarDensity κ Λ g p = originalEHScalarDensity κ Λ k p := by
  have atPoint := Filter.EventuallyEq.eq_of_nhds same
  have lcNear : leviCivitaCoefficients g =ᶠ[𝓝 p] leviCivitaCoefficients k := by
    filter_upwards [eventually_eventuallyEq_nhds.mpr same] with x hx
    funext a b c
    exact leviCivita_metric_twojet_congr g k x (metric_twojet_of_eventuallyEq g k x hx) a b c
  have lcPoint := Filter.EventuallyEq.eq_of_nhds lcNear
  have lcDeriv (a b c : Fin 4) :
      fderiv ℝ (fun x => leviCivitaCoefficients g x a b c) p =
        fderiv ℝ (fun x => leviCivitaCoefficients k x a b c) p :=
    Filter.EventuallyEq.fderiv_eq (lcNear.mono (fun x hx => congrArg (fun C => C a b c) hx))
  simp only [originalEHScalarDensity,coordinateVolumeDensity,coordinateScalarCurvature,
    coordinateRicci,loweredConnectionCurvature,connectionCurvature,atPoint,lcPoint,lcDeriv]

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X]

omit [T2Space X] in
theorem eh_compact_actual_relative_action_hasDerivAt (m : Measure X) [IsFiniteMeasure m]
    (κ Λ : ℝ) (g h : MetricField) (q : X → CoordinatePoint) (hq : Continuous q)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b))
    (negative : ∀ p, (g (q p)).det < 0) :
    HasDerivAt (fun t : ℝ => ∫ p, (originalEHScalarDensity κ Λ (ehMetricRay g h t) (q p) -
      originalEHScalarDensity κ Λ g (q p)) ∂m)
      (∫ p, ehScalarDensityVariation κ Λ g h (q p) ∂m) 0 := by
  let J : X → EHMetricJet := fun p => ehActualMetricJet g (q p)
  let H : X → EHMetricJet := fun p => ehActualMetricJet h (q p)
  have hJ : Continuous J := (eh_actual_metric_jet_contDiff g hg).continuous.comp hq
  have hH : Continuous H := (eh_actual_metric_jet_contDiff h hh).continuous.comp hq
  have regG (p : CoordinatePoint) : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p :=
    fun a b => (hg a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have regH (p : CoordinatePoint) : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p :=
    fun a b => (hh a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have result := eh_compact_jet_relative_action_hasDerivAt m κ Λ J H hJ hH negative
  have hR : (∫ p, fderiv ℝ (ehJetDensity κ Λ) (J p) (H p) ∂m) =
      ∫ p, ehScalarDensityVariation κ Λ g h (q p) ∂m := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => eh_jet_differential_is_actual_density_variation κ Λ
      g h (q p) sg sh (regG _) (regH _) (negative p))
  rw [hR] at result
  apply result.congr_of_eventuallyEq
  obtain ⟨U,hU,hzero,hn⟩ := eh_compact_jet_negative_near J H hJ hH negative
  filter_upwards [hU.mem_nhds hzero] with t ht
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have hnt : (ehMetricRay g h t (q p)).det ≠ 0 := by
    have hn' := ne_of_lt (hn t ht p)
    rw [← eh_actual_metric_jet_ray g h (q p) (regG _) (regH _) t] at hn'
    exact hn'
  change originalEHScalarDensity κ Λ (ehMetricRay g h t) (q p) -
      originalEHScalarDensity κ Λ g (q p) =
    ehJetDensity κ Λ (ehActualMetricJet g (q p) + t • ehActualMetricJet h (q p)) -
      ehJetDensity κ Λ (ehActualMetricJet g (q p))
  rw [← eh_actual_metric_jet_ray g h (q p) (regG _) (regH _) t]
  rw [eh_jet_density_is_actual κ Λ _ (q p) (eh_metric_ray_symmetric g h sg sh t)
    (eh_metric_ray_regular g h (q p) (regG _) (regH _) t) hnt,
    eh_jet_density_is_actual κ Λ g (q p) sg (regG _) (ne_of_lt (negative p))]

variable {Ω : Opens CoordinatePoint}

def ehProbeMetric (h : MetricSourceProbe Ω) : MetricField := fun p => tensorEncode (h p)

theorem eh_probe_metric_symmetric (h : MetricSourceProbe Ω) : MetricFieldSymmetric (ehProbeMetric h) :=
  fun p a b => tensorEncode_symmetric (h p) a b

theorem eh_probe_metric_smooth (h : MetricSourceProbe Ω) :
    ∀ a b, ContDiff ℝ ∞ (fun p => ehProbeMetric h p a b) := by
  have hs := tensorEncodeLinear.toContinuousLinearMap.contDiff.comp h.contDiff
  intro a b
  exact (nativeRealMatrixEntry a b).contDiff.comp hs

theorem eh_perturbed_probe_is_ray (g : MetricField) (h : MetricSourceProbe Ω) (t : ℝ) :
    originalEHMetricPerturbation g (t • h) = ehMetricRay g (ehProbeMetric h) t := by
  funext p a b
  change g p a b + tensorEncodeLinear (t • h p) a b = _
  rw [tensorEncodeLinear.map_smul]
  rfl

theorem eh_probe_metric_zero_near_outside_support (h : MetricSourceProbe Ω) (p : CoordinatePoint)
    (hp : p ∉ tsupport h) : ehProbeMetric h =ᶠ[𝓝 p] 0 := by
  have near := notMem_tsupport_iff_eventuallyEq.mp hp
  filter_upwards [near] with x hx
  change tensorEncode (h x) = 0
  rw [hx]
  exact tensorEncodeLinear.map_zero

theorem eh_relative_density_zero_outside_support (κ Λ : ℝ) (g : MetricField)
    (h : MetricSourceProbe Ω) (p : CoordinatePoint) (hp : p ∉ tsupport h) (t : ℝ) :
    originalEHScalarDensity κ Λ (ehMetricRay g (ehProbeMetric h) t) p -
      originalEHScalarDensity κ Λ g p = 0 := by
  apply sub_eq_zero.mpr
  apply eh_density_congr_of_eventuallyEq
  filter_upwards [eh_probe_metric_zero_near_outside_support h p hp] with x hx
  change ehProbeMetric h x = (0 : Tensor2) at hx
  funext a b
  simp only [ehMetricRay,hx,Matrix.zero_apply,mul_zero,add_zero]

theorem eh_density_variation_zero_outside_support (κ Λ : ℝ) (g : MetricField)
    (h : MetricSourceProbe Ω) (p : CoordinatePoint) (hp : p ∉ tsupport h)
    (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (negative : (g p).det < 0) :
    ehScalarDensityVariation κ Λ g (ehProbeMetric h) p = 0 := by
  have hd := (eh_scalar_density_variation κ Λ g (ehProbeMetric h) p sg
    (eh_probe_metric_symmetric h) hg (fun a b => (eh_probe_metric_smooth h a b).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) negative).sub_const (originalEHScalarDensity κ Λ g p)
  have zeroFn : (fun t : ℝ => originalEHScalarDensity κ Λ (ehMetricRay g (ehProbeMetric h) t) p -
      originalEHScalarDensity κ Λ g p) = fun _ => 0 :=
    funext (fun t => eh_relative_density_zero_outside_support κ Λ g h p hp t)
  rw [zeroFn] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))

theorem eh_original_relative_action_hasDerivAt (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => originalEHRelativeAction κ Λ g (t • h))
      (∫ p in (Ω : Set CoordinatePoint), ehScalarDensityVariation κ Λ g (ehProbeMetric h) p) 0 := by
  let K : Set CoordinatePoint := tsupport h
  have hK : IsCompact K := h.hasCompactSupport
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let m : Measure K := volume.comap (Subtype.val : K → CoordinatePoint)
  letI : IsFiniteMeasure m := ⟨by
    change volume.comap (Subtype.val : K → CoordinatePoint) univ < ⊤
    rw [comap_subtype_coe_apply hK.measurableSet,Set.image_univ,Subtype.range_coe]
    exact hK.measure_lt_top⟩
  have result := eh_compact_actual_relative_action_hasDerivAt m κ Λ g (ehProbeMetric h)
    (Subtype.val : K → CoordinatePoint) continuous_subtype_val sg (eh_probe_metric_symmetric h)
    hg (eh_probe_metric_smooth h) (fun p => negative p (h.tsupport_subset p.property))
  have func (t : ℝ) : (∫ p : K, (originalEHScalarDensity κ Λ (ehMetricRay g (ehProbeMetric h) t) p -
      originalEHScalarDensity κ Λ g p) ∂m) = originalEHRelativeAction κ Λ g (t • h) := by
    dsimp only [m]
    rw [integral_subtype_comap hK.measurableSet (fun p : CoordinatePoint =>
      originalEHScalarDensity κ Λ (ehMetricRay g (ehProbeMetric h) t) p -
        originalEHScalarDensity κ Λ g p)]
    unfold originalEHRelativeAction originalEHRelativeIntegrand
    rw [eh_perturbed_probe_is_ray]
    rw [← integral_indicator hK.measurableSet,← integral_indicator Ω.isOpen.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    by_cases hp : p ∈ K
    · have hpΩ := h.tsupport_subset hp
      simp only [Set.indicator_of_mem hp,Set.indicator_of_mem hpΩ]
    · have hz := eh_relative_density_zero_outside_support κ Λ g h p hp t
      by_cases hpΩ : p ∈ Ω <;> simp [hp,hpΩ,hz]
  have value : (∫ p : K, ehScalarDensityVariation κ Λ g (ehProbeMetric h) p ∂m) =
      ∫ p in (Ω : Set CoordinatePoint), ehScalarDensityVariation κ Λ g (ehProbeMetric h) p := by
    dsimp only [m]
    rw [integral_subtype_comap hK.measurableSet (fun p : CoordinatePoint =>
      ehScalarDensityVariation κ Λ g (ehProbeMetric h) p)]
    rw [← integral_indicator hK.measurableSet,← integral_indicator Ω.isOpen.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    by_cases hp : p ∈ K
    · have hpΩ := h.tsupport_subset hp
      simp only [Set.indicator_of_mem hp,Set.indicator_of_mem hpΩ]
    · by_cases hpΩ : p ∈ Ω
      · have hz := eh_density_variation_zero_outside_support κ Λ g h p hp sg
          (fun a b => (hg a b).contDiffAt.of_le
            (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) (negative p hpΩ)
        simp [hp,hpΩ,hz]
      · simp [hp,hpΩ]
  simpa only [func,value] using result

/-- Source-facing specialization to the independently declared Lorentz chart.
The frame is baseline geometric data, not a desired first-variation identity.
This does not yet establish full small-ray finite-use admission. -/
theorem eh_original_lorentz_relative_action_hasDerivAt (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (frames : ∀ p ∈ Ω, ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint, LorentzFrameAt g p B)
    (h : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => originalEHRelativeAction κ Λ g (t • h))
      (∫ p in (Ω : Set CoordinatePoint), ehScalarDensityVariation κ Λ g (ehProbeMetric h) p) 0 := by
  apply eh_original_relative_action_hasDerivAt κ Λ g sg hg
  intro p hp
  obtain ⟨B,hB⟩ := frames p hp
  exact native_lorentz_frame_determinant_negative g p B hB

end
end AASCSemanticExhaustion
