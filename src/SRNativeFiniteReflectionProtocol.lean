import SRNativeCoastingClockSource
import SRRaySourceConstructedForm

/-! Positive finite-energy coasting endpoints, two opposed original rays and
balanced identity-retaining reflection vertices: the finite ideal geometric
protocol of SR 15.5--15.7. The constitutive reflection rule is an explicit model
choice. Vertex balance is proved, not a full action/distributional Ward theorem. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def srNativeRestClock (x:E) : SRNativeClockState E:=⟨x,0,0,0⟩

theorem sr_native_positive_rest_clock_is_occupied (μ0:ℝ) (positive:0<μ0) (x:E) :
    0<srNativeClockMass μ0 (srNativeRestClock x) ∧
      srNativeClockRate μ0 (srNativeRestClock x)=1 := by
  have hp:0<srNativeClockMass μ0 (srNativeRestClock x):=by simpa [srNativeClockMass,srNativeRestClock] using positive
  exact ⟨hp,sr_native_rest_clock_has_rate_one μ0 _ hp rfl⟩

theorem sr_native_rest_clock_actual_coasting_record (μ0:ℝ) (positive:0<μ0) (x:E) (t:ℝ) :
    (srNativeClockCoastFlow μ0 t (srNativeRestClock x)).position=x ∧
      (srNativeClockCoastFlow μ0 t (srNativeRestClock x)).reading=t ∧
      (srNativeClockCoastFlow μ0 t (srNativeRestClock x)).internalEnergy=0 := by
  have hr:srNativeClockRate μ0 (srNativeRestClock x)=1:=
    (sr_native_positive_rest_clock_is_occupied μ0 positive x).2
  constructor
  · simp [srNativeClockCoastFlow,srNativeClockVelocity,srNativeRestClock]
  · constructor
    · change 0+t*srNativeClockRate μ0 (srNativeRestClock x)=t
      rw [hr]
      ring
    · rfl

def srNativePositiveRayMomentum (ε:ℝ) (n:E) : ℝ × E:=(ε,ε • n)

theorem sr_native_positive_energy_ray_is_original_future_null (ε:ℝ) (energy:0<ε)
    (n:E) (unit:‖n‖=1) :
    srNativePositiveRayMomentum ε n∈srOriginalFutureRayIncrements ∧
      srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E))
        (sr_ray_rest_clock_one (E:=E)) (srOccupiedIsotropicRaySource (E:=E))
        (srNativePositiveRayMomentum ε n)=0 := by
  have hn:‖ε • n‖=ε:=by rw [norm_smul,Real.norm_eq_abs,abs_of_pos energy,unit,mul_one]
  constructor
  · exact ⟨energy,hn⟩
  · rw [sr_full_ray_source_constructor_computes_lorentz_form_everywhere]
    change ε^2-‖ε • n‖^2=0
    rw [hn,sub_self]

theorem sr_native_balanced_reflection_preserves_total_momentum_and_endpoint
    (μ ε:ℝ) (n m:E) :
    ((μ,(0:E))+srNativePositiveRayMomentum ε n+srNativePositiveRayMomentum ε (-n))=
      ((μ,(0:E))+srNativePositiveRayMomentum ε (-m)+srNativePositiveRayMomentum ε m) := by
  apply Prod.ext
  · simp [srNativePositiveRayMomentum]
  · simp [srNativePositiveRayMomentum,smul_neg]

def srNativeProtocolDeparture (ℓ:ℝ) (k:ℕ) : ℝ × E:=((2*k:ℝ)*ℓ,0)
def srNativeProtocolReflection (ℓ:ℝ) (n:E) (k:ℕ) : ℝ × E:=(((2*k:ℝ)+1)*ℓ,ℓ • n)
def srNativeProtocolReturn (ℓ:ℝ) (k:ℕ) : ℝ × E:=((2*((k:ℝ)+1))*ℓ,0)

theorem sr_native_protocol_forward_leg_is_original_ray
    (ℓ:ℝ) (length:0<ℓ) (n:E) (unit:‖n‖=1) (k:ℕ) :
    srNativeProtocolReflection ℓ n k-srNativeProtocolDeparture (E:=E) ℓ k∈srOriginalFutureRayIncrements := by
  have he:srNativeProtocolReflection ℓ n k-srNativeProtocolDeparture (E:=E) ℓ k=(ℓ,ℓ • n):=by
    apply Prod.ext
    · simp only [srNativeProtocolReflection,srNativeProtocolDeparture,Prod.fst_sub]
      ring
    · simp [srNativeProtocolReflection,srNativeProtocolDeparture]
  rw [he]
  exact (sr_native_positive_energy_ray_is_original_future_null ℓ length n unit).1

theorem sr_native_protocol_return_leg_is_original_ray
    (ℓ:ℝ) (length:0<ℓ) (n:E) (unit:‖n‖=1) (k:ℕ) :
    srNativeProtocolReturn (E:=E) ℓ k-srNativeProtocolReflection ℓ n k∈srOriginalFutureRayIncrements := by
  have he:srNativeProtocolReturn (E:=E) ℓ k-srNativeProtocolReflection ℓ n k=(ℓ,ℓ • (-n)):=by
    apply Prod.ext
    · simp only [srNativeProtocolReturn,srNativeProtocolReflection,Prod.fst_sub]
      ring
    · simp [srNativeProtocolReturn,srNativeProtocolReflection,smul_neg]
  rw [he]
  exact (sr_native_positive_energy_ray_is_original_future_null ℓ length (-n) (by simpa using unit)).1

def srNativeCompensatingRayStart (vertex:ℝ × E) (d:ℝ) (direction:E) : ℝ × E:=
  (vertex.1-d,vertex.2-d • direction)

theorem sr_native_compensating_ray_has_actual_shared_endpoint
    (vertex:ℝ × E) (d:ℝ) (duration:0<d) (direction:E) (unit:‖direction‖=1) :
    vertex-srNativeCompensatingRayStart vertex d direction=(d,d • direction) ∧
      vertex-srNativeCompensatingRayStart vertex d direction∈srOriginalFutureRayIncrements := by
  have he:vertex-srNativeCompensatingRayStart vertex d direction=(d,d • direction):=by
    apply Prod.ext <;> simp [srNativeCompensatingRayStart]
  exact ⟨he,he ▸ (sr_native_positive_energy_ray_is_original_future_null d duration direction unit).1⟩

theorem sr_native_every_finite_roundtrip_has_same_source_clock_and_ray_records
    (μ0 ℓ ε:ℝ) (mass:0<μ0) (length:0<ℓ) (energy:0<ε)
    (n:E) (unit:‖n‖=1) (N:ℕ) :
    (0<srNativeClockMass μ0 (srNativeRestClock (0:E))) ∧
    (0<srNativeClockMass μ0 (srNativeRestClock (ℓ • n))) ∧
    (∀ k:Fin N,
      srNativeProtocolReflection ℓ n k.val-srNativeProtocolDeparture (E:=E) ℓ k.val∈srOriginalFutureRayIncrements ∧
      srNativeProtocolReturn (E:=E) ℓ k.val-srNativeProtocolReflection ℓ n k.val∈srOriginalFutureRayIncrements ∧
      (srNativeClockCoastFlow μ0 (srNativeProtocolReturn (E:=E) ℓ k.val).1 (srNativeRestClock (0:E))).reading=
        2*((k.val:ℝ)+1)*ℓ) ∧
    srNativePositiveRayMomentum ε n∈srOriginalFutureRayIncrements := by
  refine ⟨(sr_native_positive_rest_clock_is_occupied μ0 mass _).1,
    (sr_native_positive_rest_clock_is_occupied μ0 mass _).1,?_,
    (sr_native_positive_energy_ray_is_original_future_null ε energy n unit).1⟩
  intro k
  refine ⟨sr_native_protocol_forward_leg_is_original_ray ℓ length n unit k.val,
    sr_native_protocol_return_leg_is_original_ray ℓ length n unit k.val,?_⟩
  exact (sr_native_rest_clock_actual_coasting_record μ0 mass (0:E) _).2.1

#print axioms sr_native_positive_rest_clock_is_occupied
#print axioms sr_native_rest_clock_actual_coasting_record
#print axioms sr_native_positive_energy_ray_is_original_future_null
#print axioms sr_native_balanced_reflection_preserves_total_momentum_and_endpoint
#print axioms sr_native_protocol_forward_leg_is_original_ray
#print axioms sr_native_protocol_return_leg_is_original_ray
#print axioms sr_native_compensating_ray_has_actual_shared_endpoint
#print axioms sr_native_every_finite_roundtrip_has_same_source_clock_and_ray_records
end
end AASCMetricConstruction
