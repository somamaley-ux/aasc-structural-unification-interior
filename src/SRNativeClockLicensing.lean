import SRNativeFiniteReflectionProtocol
import SRConstructedIntervalCalibration

/-! An actual nonempty Metricity-style original-use safe region for the
zero-force coasting clock task. Every real characteristic redescription and
every original marked time is retained. This proves a qualified duration use;
it does not identify a minimal physical dependency interface for all MD. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def srNativeClockRedescription {ID:Type*} (μ0 h:ℝ)
    (r:ID × (ℝ × SRNativeClockState E)) : ID × (ℝ × SRNativeClockState E):=
  (r.1,r.2.1+h,srNativeClockCoastFlow μ0 h r.2.2)

theorem sr_native_clock_redescription_preserves_every_original_marked_record
    {ID:Type*} (μ0 h:ℝ) (r:ID × (ℝ × SRNativeClockState E)) (σ:ℝ) :
    srNativeCoastingMarkedRecord μ0 (srNativeClockRedescription μ0 h r) σ=
      srNativeCoastingMarkedRecord μ0 r σ := by
  apply Prod.ext
  · rfl
  · change srNativeClockCoastFlow μ0 (σ-(r.2.1+h)) (srNativeClockCoastFlow μ0 h r.2.2)=
      srNativeClockCoastFlow μ0 (σ-r.2.1) r.2.2
    rw [sr_native_coasting_flow_composition]
    congr 1
    ring

structure SRNativeClockUse (E:Type*) where
  record:Fin 2 × (ℝ × SRNativeClockState E)
  start:ℝ
  finish:ℝ
  claimed:ℝ

def srNativeClockActualInterval (μ0:ℝ) (c:SRNativeClockUse E) : ℝ:=
  (srNativeCoastingMarkedRecord μ0 c.record c.finish).2.reading-
    (srNativeCoastingMarkedRecord μ0 c.record c.start).2.reading

def srNativeClockUseValid (μ0:ℝ) (c:SRNativeClockUse E) : Prop:=
  0<srNativeClockMass μ0 c.record.2.2 ∧ c.start≤c.finish ∧
    c.claimed=srNativeClockActualInterval μ0 c

def srNativeClockUseRedescription (μ0 h:ℝ) (c:SRNativeClockUse E) : SRNativeClockUse E:=
  {c with record:=srNativeClockRedescription μ0 h c.record}

theorem sr_native_clock_original_use_domain_and_answer_preserved (μ0 h:ℝ) (c:SRNativeClockUse E) :
    srNativeClockUseValid μ0 (srNativeClockUseRedescription μ0 h c) ↔ srNativeClockUseValid μ0 c := by
  have he:srNativeClockActualInterval μ0 (srNativeClockUseRedescription μ0 h c)=
      srNativeClockActualInterval μ0 c:=by
    unfold srNativeClockActualInterval
    simp only [srNativeClockUseRedescription,
      sr_native_clock_redescription_preserves_every_original_marked_record]
  change (0<srNativeClockMass μ0 c.record.2.2 ∧ c.start≤c.finish ∧
    c.claimed=srNativeClockActualInterval μ0 (srNativeClockUseRedescription μ0 h c)) ↔ _
  rw [he]
  rfl

def srNativeClockFiniteRedescriptions (μ0:ℝ) (path:List ℝ) (c:SRNativeClockUse E) : SRNativeClockUse E:=
  path.foldl (fun c h=>srNativeClockUseRedescription μ0 h c) c

theorem sr_native_clock_every_finite_declared_redescription_is_safe
    (μ0:ℝ) (c:SRNativeClockUse E) (valid:srNativeClockUseValid μ0 c) :
    ∀ path:List ℝ,srNativeClockUseValid μ0 (srNativeClockFiniteRedescriptions μ0 path c) := by
  intro path
  induction path generalizing c with
  | nil=>exact valid
  | cons h path ih=>
    exact ih _ ((sr_native_clock_original_use_domain_and_answer_preserved μ0 h c).mpr valid)

def srNativeClockSafeRegion (μ0:ℝ) : Set (SRNativeClockUse E):=
  {c|∀ path:List ℝ,srNativeClockUseValid μ0 (srNativeClockFiniteRedescriptions μ0 path c)}

theorem sr_native_clock_greatest_original_safe_region_computed (μ0:ℝ) (c:SRNativeClockUse E) :
    c∈srNativeClockSafeRegion μ0 ↔ srNativeClockUseValid μ0 c :=
  ⟨fun h=>h [],sr_native_clock_every_finite_declared_redescription_is_safe μ0 c⟩

theorem sr_native_physical_rest_duration_safe_region_is_nonempty (μ0:ℝ) (positive:0<μ0) :
    (srNativeClockSafeRegion (E:=E) μ0).Nonempty := by
  let c:SRNativeClockUse E:=⟨(0,0,srNativeRestClock (0:E)),0,1,1⟩
  refine ⟨c,(sr_native_clock_greatest_original_safe_region_computed μ0 c).mpr ?_⟩
  refine ⟨(sr_native_positive_rest_clock_is_occupied μ0 positive _).1,by norm_num,?_⟩
  change 1=(srNativeClockCoastFlow μ0 (1-0) (srNativeRestClock (0:E))).reading-
    (srNativeClockCoastFlow μ0 (0-0) (srNativeRestClock (0:E))).reading
  rw [(sr_native_rest_clock_actual_coasting_record μ0 positive (0:E) _).2.1,
      (sr_native_rest_clock_actual_coasting_record μ0 positive (0:E) _).2.1]
  ring

theorem sr_original_real_interval_calibration_equals_actual_rest_clock_receipt
    (μ0:ℝ) (positive:0<μ0) (x:E) (s t:ℝ) :
    srConstructedNormalizedIntervalDuration (A:=ℝ) (t-s)=
      (srNativeClockCoastFlow μ0 t (srNativeRestClock x)).reading-
      (srNativeClockCoastFlow μ0 s (srNativeRestClock x)).reading := by
  have he:srConstructedNormalizedIntervalDuration (A:=ℝ)=
      (⟨AddMonoidHom.id ℝ,monotone_id⟩:ℝ →+o ℝ):=
    sr_same_original_interval_order_and_unit_force_same_duration _ _ Archimedean.embedReal_one rfl
  rw [he,(sr_native_rest_clock_actual_coasting_record μ0 positive x t).2.1,
    (sr_native_rest_clock_actual_coasting_record μ0 positive x s).2.1]
  rfl

#print axioms sr_native_clock_redescription_preserves_every_original_marked_record
#print axioms sr_native_clock_original_use_domain_and_answer_preserved
#print axioms sr_native_clock_every_finite_declared_redescription_is_safe
#print axioms sr_native_clock_greatest_original_safe_region_computed
#print axioms sr_native_physical_rest_duration_safe_region_is_nonempty
#print axioms sr_original_real_interval_calibration_equals_actual_rest_clock_receipt
end
end AASCMetricConstruction
