import OriginalPreparedFieldRestoration

/-! A concrete original continuation distinguishes every nonzero admitted
metric-operand change. The old bounded analytic domain supplies a first exit
along the actual direction. The same subsequent vary operation then emits an
admitted original request on one operand and the old typed rejection on the
other. This is not a definition of a standing-localization burden or full F_D. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem prepared_metric_direction_has_nonzero_entry (K : MetricSourceProbe Ω) (nonzero : K ≠ 0) :
    ∃ (p : CoordinatePoint) (i j : Fin 4),tensorEncode (K p) i j ≠ 0 := by
  by_contra! allZero
  apply nonzero
  apply TestFunction.ext
  intro p
  have encoded : tensorEncode (K p) = (0 : Tensor2) := by
    ext i j
    exact allZero p i j
  have decodedZero : tensorDecode (0 : Tensor2) = (0 : Fin 10 → ℝ) := tensorDecodeLinear.map_zero
  simpa only [tensor_decode_encode,decodedZero] using congrArg tensorDecode encoded

theorem prepared_metric_integer_ray_exits_old_domain
    (H K : MetricSourceProbe Ω) (nonzero : K ≠ 0) :
    ∃ n : ℕ,H + (n : ℝ) • K ∉ wickOriginalMetricNeighborhood Ω := by
  obtain ⟨p,i,j,hk⟩ := prepared_metric_direction_has_nonzero_entry Ω K nonzero
  let h : ℝ := tensorEncode (H p) i j
  let k : ℝ := tensorEncode (K p) i j
  have kpos : 0 < |k| := abs_pos.mpr hk
  obtain ⟨n,hn⟩ := exists_nat_gt ((|h|+1)/|k|)
  refine ⟨n,?_⟩
  intro inside
  have bound := original_eh_act_coefficient_bound (H + (n : ℝ) • K) inside p i j
  have entry : tensorEncode ((H + (n : ℝ) • K) p) i j = h + (n : ℝ)*k := by
    change tensorEncodeLinear (H p + (n : ℝ) • K p) i j = _
    rw [map_add,map_smul]
    rfl
  rw [entry] at bound
  have lower : |h|+1 < (n : ℝ)*|k| := (div_lt_iff₀ kpos).mp hn
  have tri : |(n : ℝ)*k| ≤ |h+(n : ℝ)*k|+|h| := by
    calc
      |(n : ℝ)*k| = |(h+(n : ℝ)*k)-h| := congrArg abs (by ring)
      _ ≤ |h+(n : ℝ)*k|+|h| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (h+(n : ℝ)*k) 0 h
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)] at tri
  linarith

theorem prepared_metric_original_boundary_separates_translation
    (H K : MetricSourceProbe Ω) (admitted : H ∈ wickOriginalMetricNeighborhood Ω)
    (nonzero : K ≠ 0) :
    ∃ L : MetricSourceProbe Ω,
      H + L ∈ wickOriginalMetricNeighborhood Ω ∧
      (H+K) + L ∉ wickOriginalMetricNeighborhood Ω := by
  have exits := prepared_metric_integer_ray_exits_old_domain Ω H K nonzero
  let n := Nat.find exits
  have hn : H + (n : ℝ) • K ∉ wickOriginalMetricNeighborhood Ω := Nat.find_spec exits
  have npos : 0 < n := by
    by_contra h
    have nz : n = 0 := by omega
    apply hn
    simpa only [nz,Nat.cast_zero,zero_smul,add_zero] using admitted
  have before : H + ((n-1 : ℕ) : ℝ) • K ∈ wickOriginalMetricNeighborhood Ω := by
    by_contra outside
    have minimum : n ≤ n-1 := Nat.find_min' exits outside
    omega
  refine ⟨((n-1 : ℕ) : ℝ) • K,before,?_⟩
  have index : (n : ℝ) = ((n-1 : ℕ) : ℝ)+1 := by
    exact_mod_cast (show n = (n-1)+1 by omega)
  have equal : (H+K) + ((n-1 : ℕ) : ℝ) • K = H + (n : ℝ) • K := by
    rw [index,add_smul,one_smul]
    abel
  rw [equal]
  exact hn

theorem prepared_metric_small_nonzero_admitted_change
    (H K : MetricSourceProbe Ω) (admitted : H ∈ wickOriginalMetricNeighborhood Ω)
    (nonzero : K ≠ 0) :
    ∃ c : ℝ,0 < c ∧ H + c • K ∈ wickOriginalMetricNeighborhood Ω ∧ c • K ≠ 0 := by
  have around := original_eh_actual_act_curve_admitted H admitted K
  obtain ⟨ε,positive,ball⟩ := Metric.mem_nhds_iff.mp around
  have halfPositive : 0 < ε/2 := half_pos positive
  refine ⟨ε/2,halfPositive,ball ?_,smul_ne_zero halfPositive.ne' nonzero⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos halfPositive]
  linarith

theorem prepared_metric_future_request_domain_complete
    (H J : MetricSourceProbe Ω) (admitted : H ∈ wickOriginalMetricNeighborhood Ω) :
    (∀ L : MetricSourceProbe Ω,
      H+L ∈ wickOriginalMetricNeighborhood Ω ↔ J+L ∈ wickOriginalMetricNeighborhood Ω) ↔ H=J := by
  constructor
  · intro same
    by_contra different
    have nonzero : J-H ≠ 0 := sub_ne_zero.mpr (fun same => different same.symm)
    obtain ⟨L,left,right⟩ :=
      prepared_metric_original_boundary_separates_translation Ω H (J-H) admitted nonzero
    have cancel : H+(J-H) = J := by abel
    rw [cancel] at right
    exact right ((same L).mp left)
  · rintro rfl
    exact fun _ => Iff.rfl

theorem prepared_future_request_admission_recovers_actual_operand
    (z w : PreparedOriginal a s Ω) :
    (∀ L : MetricSourceProbe Ω,
      (∃ v,preparedEventAnswer a s Ω ⟨z,preparedFiniteRequest a Ω
        ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val+L)⟩ = some v) ↔
      ∃ v,preparedEventAnswer a s Ω ⟨w,preparedFiniteRequest a Ω
        ((originalEHPreparedAct s Ω (kgOriginalObject a) w).val+L)⟩ = some v) ↔
    (originalEHPreparedAct s Ω (kgOriginalObject a) z).val =
      (originalEHPreparedAct s Ω (kgOriginalObject a) w).val := by
  simp only [prepared_finite_request_admission_exact]
  exact prepared_metric_future_request_domain_complete Ω _ _
    (originalEHPreparedAct s Ω (kgOriginalObject a) z).property

theorem prepared_quantum_and_future_request_admission_recover_same_use
    (z w : PreparedOriginal a s Ω) :
    (kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) z =
        kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) w ∧
      ∀ L : MetricSourceProbe Ω,
        (∃ v,preparedEventAnswer a s Ω ⟨z,preparedFiniteRequest a Ω
          ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val+L)⟩ = some v) ↔
        ∃ v,preparedEventAnswer a s Ω ⟨w,preparedFiniteRequest a Ω
          ((originalEHPreparedAct s Ω (kgOriginalObject a) w).val+L)⟩ = some v) ↔ z=w := by
  constructor
  · rintro ⟨quantum,requests⟩
    apply kg_prepared_joint_projections_faithful s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) z w quantum
    rw [kg_prepared_metric_field_eq,kg_prepared_metric_field_eq]
    exact congrArg wickOriginalFiniteMetric
      ((prepared_future_request_admission_recovers_actual_operand a s Ω z w).mp requests)
  · rintro rfl
    exact ⟨rfl,fun _ => Iff.rfl⟩

theorem prepared_history_same_next_variation_separates_original_requests
    (K : MetricSourceProbe Ω) (nonzero : K ≠ 0) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    ∃ L : MetricSourceProbe Ω,
      preparedEventFailure a s Ω
        ⟨preparedOriginalBase a s Ω x.locus,preparedFiniteRequest a Ω
          ((originalEHPreparedAct s Ω (kgOriginalObject a)
            (preparedOriginalBase a s Ω x.locus)).val + L)⟩ = none ∧
      preparedEventFailure a s Ω
        ⟨preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus,
          preparedFiniteRequest a Ω
            ((originalEHPreparedAct s Ω (kgOriginalObject a)
              (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus)).val + L)⟩ =
                some .originalMetricRejection := by
  obtain ⟨L,left,right⟩ := prepared_metric_original_boundary_separates_translation Ω
    (originalEHPreparedAct s Ω (kgOriginalObject a) (preparedOriginalBase a s Ω x.locus)).val
    K (originalEHPreparedAct s Ω (kgOriginalObject a) (preparedOriginalBase a s Ω x.locus)).property nonzero
  refine ⟨L,?_,?_⟩
  · rw [prepared_finite_request_failure,if_pos left]
  · rw [prepared_finite_request_failure,prepared_history_vary_operand a s Ω K x inside,if_neg right]

theorem prepared_history_same_next_variation_emits_distinct_diagnostics
    (K : MetricSourceProbe Ω) (nonzero : K ≠ 0) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    ∃ (L : MetricSourceProbe Ω) (e f : PreparedEvent a s Ω),
      (preparedHistoryVary a s Ω L x).events = x.events ++ [e] ∧
      (preparedHistoryVary a s Ω L (preparedHistoryVary a s Ω K x)).events =
        (preparedHistoryVary a s Ω K x).events ++ [f] ∧
      preparedEventFailure a s Ω e = none ∧
      preparedEventFailure a s Ω f = some .originalMetricRejection := by
  obtain ⟨L,left,right⟩ :=
    prepared_history_same_next_variation_separates_original_requests a s Ω K nonzero x inside
  refine ⟨L,⟨preparedOriginalBase a s Ω x.locus,preparedFiniteRequest a Ω
      ((originalEHPreparedAct s Ω (kgOriginalObject a)
        (preparedOriginalBase a s Ω x.locus)).val+L)⟩,
    ⟨preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus,
      preparedFiniteRequest a Ω ((originalEHPreparedAct s Ω (kgOriginalObject a)
        (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus)).val+L)⟩,
    prepared_history_vary_events a s Ω L x,
    prepared_history_vary_events a s Ω L (preparedHistoryVary a s Ω K x),left,right⟩

end
end AASCKleinGordon
