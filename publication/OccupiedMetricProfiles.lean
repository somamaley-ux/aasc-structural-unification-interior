import CompactMetricResponse
import KGLicensedEHReceiver
import OriginalPreparedContinuationSeparation

/-! A physical requirement can be tested on what an already safe history
represents. The original fixed source supplies both the operand and the
compact action derivatives; the candidate supplies only a density. -/

noncomputable section
set_option autoImplicit false

namespace AASCOccupiedProfiles

/-- Keeping an original profile occupied allows a change of representative.
The inclusion assumption expresses the direction of the added restriction. -/
theorem profile_image_eq_iff {X P : Type*} (F : X → P) {S T : Set X} (sub : T ⊆ S) :
    F '' T = F '' S ↔ ∀ x ∈ S, ∃ y ∈ T, F y = F x := by
  constructor
  · intro same x hx
    have mem : F x ∈ F '' S := ⟨x, hx, rfl⟩
    rwa [← same] at mem
  · intro cover
    apply Set.Subset.antisymm (Set.image_mono sub)
    rintro _ ⟨x, hx, rfl⟩
    exact cover x hx

/-- An original profile is genuinely lost exactly when none of its original
representatives remains among the survivors. -/
theorem lost_profile_iff {X P : Type*} (F : X → P) {S T : Set X} (sub : T ⊆ S) :
    F '' T ≠ F '' S ↔ ∃ x ∈ S, ∀ y ∈ T, F y ≠ F x := by
  classical
  rw [ne_eq, profile_image_eq_iff F sub]
  push_neg
  rfl

open AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
open AASCSemanticExhaustion AASCKleinGordon AASCKleinGordon.CanonicalLicensing
open AASCProjectionObservations TopologicalSpace MeasureTheory

abbrev AdmittedOperand (Ω : Opens CoordinatePoint) :=
  {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}

def currentOperand (a : Parameters) (Ω : Opens CoordinatePoint)
    (h : RestrictedRawHistory a Ω) : AdmittedOperand Ω :=
  (restrictedRawHistoryRun a Ω h).current.act

/-- Add one local condition on the current metric operand while retaining
the old records, declared edges, warrants and continuation obligations. -/
def comparedMetricTask (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (κ Λ : ℝ) (accept : AdmittedOperand Ω → Prop) :=
  { originalMetricTask a s Ω κ Λ with originalLocal := fun h =>
      (originalMetricTask a s Ω κ Λ).originalLocal h ∧ accept (currentOperand a Ω h) }

/-- Every analytically admitted operand already has an original safe history.
No nonemptiness or surjectivity assumption on original histories is needed. -/
theorem original_safe_operand_image (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (κ Λ : ℝ) (hk : κ ≠ 0) :
    currentOperand a Ω '' canonicalSafeUses (originalMetricTask a s Ω κ Λ) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro H
  let h : RestrictedRawHistory a Ω := ⟨1, ⟨kgFamilyVacuum a, H⟩, []⟩
  exact ⟨h, original_history_is_safe a s Ω κ Λ hk h, rfl⟩

/-- For an operand-dependent requirement, preserving all originally occupied
operand profiles is equivalent to passing the requirement on every admitted
operand. The reverse direction preserves future uses as well as the present. -/
theorem compared_safe_operand_image_iff (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (κ Λ : ℝ) (hk : κ ≠ 0) (accept : AdmittedOperand Ω → Prop) :
    currentOperand a Ω '' canonicalSafeUses (comparedMetricTask a s Ω κ Λ accept) =
      currentOperand a Ω '' canonicalSafeUses (originalMetricTask a s Ω κ Λ) ↔
      ∀ H, accept H := by
  let D := comparedMetricTask a s Ω κ Λ accept
  rw [original_safe_operand_image a s Ω κ Λ hk]
  constructor
  · intro same H
    have mem : H ∈ currentOperand a Ω '' canonicalSafeUses D := by rw [same]; trivial
    obtain ⟨h, safe, rfl⟩ := mem
    have localTest := (original_safe_region_is_sound (originalLocalTest D)
      (declaredOriginalEdge D) (originalEdgeTest D) h safe).1
    exact localTest.2.2.1.2
  · intro allPass
    have sound : OriginalSoundRegion (originalLocalTest D) (declaredOriginalEdge D)
        (originalEdgeTest D) Set.univ := by
      intro h _
      obtain ⟨localTest, edges⟩ := original_history_region_postfixed a s Ω κ Λ hk (Set.mem_univ h)
      exact ⟨⟨localTest.1, localTest.2.1, ⟨localTest.2.2.1, allPass _⟩, localTest.2.2.2⟩, edges⟩
    apply Set.eq_univ_of_forall
    intro H
    let h : RestrictedRawHistory a Ω := ⟨1, ⟨kgFamilyVacuum a, H⟩, []⟩
    exact ⟨h, original_sound_region_is_safe _ _ _ Set.univ sound h (Set.mem_univ _), rfl⟩

variable {Ω : Opens CoordinatePoint}

private theorem compact_readings_of_density (κ Λ : ℝ) (hk : κ ≠ 0)
    (H : AdmittedOperand Ω) (d : Fin 10 → CoordinatePoint → ℝ)
    (eqOn : ∀ p ∈ Ω, ∀ i, d i p = ehComputedSourceDensity κ Λ (originalEHActMetric H.val) i p) :
    MatchesCompactReadings κ Λ H.val d := by
  intro i φ
  let g := originalEHActMetric H.val
  have integrands (p : CoordinatePoint) :
      d i p * φ p = ehComputedSourceDensity κ Λ g i p * φ p := by
    by_cases hp : p ∈ Ω
    · rw [eqOn p hp i]
    · have zero : φ p = 0 := by
        by_contra nz
        exact hp (φ.tsupport_subset (subset_tsupport φ nz))
      rw [zero, mul_zero, mul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall integrands),
    (original_eh_actual_act_hasDerivAt κ Λ hk H.val H.property _).deriv]
  exact (eh_original_euler_response_density κ Λ hk g (original_eh_act_metric_symmetric _)
    (original_eh_act_metric_smooth _) (fun p _ => original_eh_act_metric_negative _ H.property p) i φ).symm

/-- Exact conservation theorem for the specified EH action. The rival is a
continuous ten-component response density on each original operand. It is
tested only against original compact directional derivatives. No smoothness
in the operand or ansatz on the rival's metric dependence is used. -/
theorem eh_preserves_occupied_operands_iff (a : Parameters) (s : ℝ)
    (κ Λ : ℝ) (hk : κ ≠ 0) (d : AdmittedOperand Ω → Fin 10 → CoordinatePoint → ℝ)
    (continuous : ∀ H i, ContinuousOn (d H i) (Ω : Set CoordinatePoint)) :
    currentOperand a Ω '' canonicalSafeUses (comparedMetricTask a s Ω κ Λ
      (fun H => MatchesCompactReadings κ Λ H.val (d H))) =
        currentOperand a Ω '' canonicalSafeUses (originalMetricTask a s Ω κ Λ) ↔
      ∀ H p, p ∈ Ω → ∀ i, d H i p = ehComputedSourceDensity κ Λ (originalEHActMetric H.val) i p := by
  rw [compared_safe_operand_image_iff a s Ω κ Λ hk]
  exact ⟨fun pass H => metric_density_of_compact_readings κ Λ hk H.val H.property
    (d H) (continuous H) (pass H), fun same H => compact_readings_of_density κ Λ hk H (d H) (same H)⟩

/-- A differing density at one interior point loses this very operand
from the strengthened safe task and fails an original compact action test. -/
theorem unequal_density_loses_operand (a : Parameters) (s : ℝ)
    (κ Λ : ℝ) (hk : κ ≠ 0) (d : AdmittedOperand Ω → Fin 10 → CoordinatePoint → ℝ)
    (H : AdmittedOperand Ω) (continuous : ∀ i, ContinuousOn (d H i) (Ω : Set CoordinatePoint))
    (p : CoordinatePoint) (hp : p ∈ Ω) (i : Fin 10)
    (different : d H i p ≠ ehComputedSourceDensity κ Λ (originalEHActMetric H.val) i p) :
    H ∈ currentOperand a Ω '' canonicalSafeUses (originalMetricTask a s Ω κ Λ) ∧
    H ∉ currentOperand a Ω '' canonicalSafeUses (comparedMetricTask a s Ω κ Λ
      (fun K => MatchesCompactReadings κ Λ K.val (d K))) ∧
    ∃ (j : Fin 10) (φ : ScalarSourceProbe Ω), (∫ x, d H j x * φ x) ≠
      (2 / symmetricSourceWeight j) * deriv (fun t : ℝ =>
        originalEHRelativeAction κ Λ wickNativeFlatMetric (H.val + t • sourceTestInsertion j φ)) 0 := by
  classical
  have fails : ¬ MatchesCompactReadings κ Λ H.val (d H) := fun pass =>
    different (metric_density_of_compact_readings κ Λ hk H.val H.property (d H)
      continuous pass p hp i)
  refine ⟨?_, ?_, ?_⟩
  · rw [original_safe_operand_image a s Ω κ Λ hk]
    trivial
  · rintro ⟨h, safe, same⟩
    let D := comparedMetricTask a s Ω κ Λ (fun K => MatchesCompactReadings κ Λ K.val (d K))
    have localTest := (original_safe_region_is_sound (originalLocalTest D)
      (declaredOriginalEdge D) (originalEdgeTest D) h safe).1
    apply fails
    rw [← same]
    exact localTest.2.2.1.2
  · unfold MatchesCompactReadings at fails
    push_neg at fails
    exact fails

/-- The observed profile records only which displacements of the current
operand return some original answer to a finite metric request. It need
not contain the operand as a reported coordinate. -/
def futureRequestProfile (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (h : RestrictedRawHistory a Ω) : Set (MetricSourceProbe Ω) :=
  {L | ∃ v, preparedEventAnswer a s Ω
    ⟨restrictedRawReceive a s Ω (restrictedRawHistoryRun a Ω h).current,
      preparedFiniteRequest a Ω ((currentOperand a Ω h).val + L)⟩ = some v}

/-- Testing preservation using only original success/failure patterns of
future requests gives the same characterization of the rival density. -/
theorem eh_preserves_future_request_profiles_iff (a : Parameters) (s : ℝ)
    (κ Λ : ℝ) (hk : κ ≠ 0) (d : AdmittedOperand Ω → Fin 10 → CoordinatePoint → ℝ)
    (continuous : ∀ H i, ContinuousOn (d H i) (Ω : Set CoordinatePoint)) :
    futureRequestProfile a s Ω '' canonicalSafeUses (comparedMetricTask a s Ω κ Λ
      (fun H => MatchesCompactReadings κ Λ H.val (d H))) =
        futureRequestProfile a s Ω '' canonicalSafeUses (originalMetricTask a s Ω κ Λ) ↔
      ∀ H p, p ∈ Ω → ∀ i, d H i p = ehComputedSourceDensity κ Λ (originalEHActMetric H.val) i p := by
  let accepted := fun H : AdmittedOperand Ω =>
    {L : MetricSourceProbe Ω | H.val + L ∈ wickOriginalMetricNeighborhood Ω}
  have faithful : Function.Injective accepted := by
    intro H J same
    apply Subtype.ext
    apply (prepared_metric_future_request_domain_complete Ω H.val J.val H.property).mp
    intro L
    exact Set.ext_iff.mp same L
  have image (U : Set (RestrictedRawHistory a Ω)) :
      futureRequestProfile a s Ω '' U = accepted '' (currentOperand a Ω '' U) := by
    rw [Set.image_image]
    apply congrArg (fun f => f '' U)
    funext h
    ext L
    exact prepared_finite_request_admission_exact a s Ω _ _
  rw [image, image, Set.image_eq_image faithful]
  exact eh_preserves_occupied_operands_iff a s κ Λ hk d continuous

end AASCOccupiedProfiles
