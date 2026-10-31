import OriginalEinsteinHilbertDensity

/-! Actual gravitational action/evaluation of WDW-4B (71), in a fixed chart
with compact relative metric variations. Finite-use domain checks are analytic
source/target Lorentz and integration checks, not desired response laws.
The total raw integral is not confused with an admitted partial evaluation.
The variation operand is retained even when evaluation fails. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter TopologicalSpace MeasureTheory
open scoped Topology
variable {Ω : Opens CoordinatePoint}

def originalEHMetricPerturbation (g : MetricField) (h : MetricSourceProbe Ω) : MetricField :=
  fun p a b => g p a b + tensorEncode (h p) a b

def originalEHRelativeIntegrand (κ Λ : ℝ) (g : MetricField) (h : MetricSourceProbe Ω) :
    CoordinatePoint → ℝ :=
  fun p => originalEHScalarDensity κ Λ (originalEHMetricPerturbation g h) p -
    originalEHScalarDensity κ Λ g p

def originalEHRelativeAction (κ Λ : ℝ) (g : MetricField) (h : MetricSourceProbe Ω) : ℝ :=
  ∫ p in (Ω : Set CoordinatePoint), originalEHRelativeIntegrand κ Λ g h p

def OriginalEHFiniteUseDomain (κ Λ : ℝ) (g : MetricField) (h : MetricSourceProbe Ω) : Prop :=
  κ ≠ 0 ∧ (∀ p ∈ Ω, C2LorentzMetricAt g p) ∧
    (∀ p ∈ Ω, C2LorentzMetricAt (originalEHMetricPerturbation g h) p) ∧
      IntegrableOn (originalEHRelativeIntegrand κ Λ g h) (Ω : Set CoordinatePoint)

def originalEHFiniteUse (κ Λ : ℝ) (g : MetricField) (h : MetricSourceProbe Ω) :
    MetricSourceProbe Ω × Option ℝ := by
  classical
  exact (h, if OriginalEHFiniteUseDomain κ Λ g h then some (originalEHRelativeAction κ Λ g h) else none)

theorem original_eh_finite_use_retains_operand (κ Λ : ℝ) (g : MetricField) (h : MetricSourceProbe Ω) :
    (originalEHFiniteUse κ Λ g h).1 = h := rfl

theorem original_eh_finite_use_success_exact (κ Λ : ℝ) (g : MetricField)
    (h : MetricSourceProbe Ω) (a : ℝ) :
    (originalEHFiniteUse κ Λ g h).2 = some a ↔
      OriginalEHFiniteUseDomain κ Λ g h ∧ originalEHRelativeAction κ Λ g h = a := by
  classical
  by_cases valid : OriginalEHFiniteUseDomain κ Λ g h <;> simp [originalEHFiniteUse,valid]

theorem original_eh_finite_use_failure_exact (κ Λ : ℝ) (g : MetricField) (h : MetricSourceProbe Ω) :
    (originalEHFiniteUse κ Λ g h).2 = none ↔ ¬ OriginalEHFiniteUseDomain κ Λ g h := by
  classical
  by_cases valid : OriginalEHFiniteUseDomain κ Λ g h <;> simp [originalEHFiniteUse,valid]

theorem original_eh_zero_perturbation (g : MetricField) :
    originalEHMetricPerturbation g (0 : MetricSourceProbe Ω) = g := by
  funext p a b
  change g p a b + tensorEncode (0 : Fin 10 → ℝ) a b = g p a b
  rw [show tensorEncode (0 : Fin 10 → ℝ) = 0 from tensorEncodeLinear.map_zero]
  simp only [Pi.zero_apply,add_zero]

theorem original_eh_zero_relative_integrand (κ Λ : ℝ) (g : MetricField) :
    originalEHRelativeIntegrand κ Λ g (0 : MetricSourceProbe Ω) = 0 := by
  funext p
  simp only [originalEHRelativeIntegrand,original_eh_zero_perturbation,sub_self,Pi.zero_apply]

theorem original_eh_zero_relative_action (κ Λ : ℝ) (g : MetricField) :
    originalEHRelativeAction κ Λ g (0 : MetricSourceProbe Ω) = 0 := by
  rw [originalEHRelativeAction,original_eh_zero_relative_integrand]
  simp only [Pi.zero_apply,integral_zero]

/-- A defined zero remains distinct from failure. The baseline is occupied
on precisely the explicitly declared regular Lorentz chart and nonzero κ. -/
theorem original_eh_zero_use_is_admitted (κ Λ : ℝ) (g : MetricField)
    (coupling : κ ≠ 0) (domain : ∀ p ∈ Ω, C2LorentzMetricAt g p) :
    (originalEHFiniteUse κ Λ g (0 : MetricSourceProbe Ω)).2 = some 0 := by
  apply (original_eh_finite_use_success_exact κ Λ g 0 0).mpr
  refine ⟨⟨coupling,domain,?_,?_⟩,original_eh_zero_relative_action κ Λ g⟩
  · rw [original_eh_zero_perturbation]
    exact domain
  · rw [original_eh_zero_relative_integrand]
    exact integrableOn_zero

def originalEHCosmologicalMatrixDensity (κ Λ : ℝ) (G : Tensor2) : ℝ :=
  (-Λ / κ) * Real.sqrt (-G.det)

theorem original_eh_density_splits_curvature_and_volume (κ Λ : ℝ) (g : MetricField)
    (p : CoordinatePoint) :
    originalEHScalarDensity κ Λ g p =
      coordinateVolumeDensity g p * coordinateScalarCurvature g p / (2 * κ) +
        originalEHCosmologicalMatrixDensity κ Λ (g p) := by
  unfold originalEHScalarDensity originalEHCosmologicalMatrixDensity coordinateVolumeDensity
  ring

/-- An actual variation calculation for the volume summand, including the
original Lorentz-domain sign. This does not assume any rank-two Euler tensor. -/
theorem original_eh_lorentz_volume_variation (G H : Tensor2) (negative : G.det < 0) :
    HasDerivAt (fun t : ℝ => Real.sqrt (-(G + t • H).det))
      ((1/2 : ℝ) * Real.sqrt (-G.det) * Matrix.trace (G⁻¹ * H)) 0 := by
  have nondegenerate := ne_of_lt negative
  have inverse := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr nondegenerate)
  have volume := native_real_clock_volume_path_hasDerivAt G G⁻¹ H inverse nondegenerate
  have determinant := native_real_metric_determinant_path_hasDerivAt G G⁻¹ H inverse
  have near : ∀ᶠ t in 𝓝 (0 : ℝ), (G + t • H).det < 0 :=
    determinant.continuousAt.tendsto.eventually
      (isOpen_Iio.mem_nhds (by simpa using negative))
  have atBase : nativeRealClockVolume G = Real.sqrt (-G.det) := by
    simp only [nativeRealClockVolume,abs_of_neg negative]
  rw [atBase] at volume
  apply volume.congr_of_eventuallyEq
  filter_upwards [near] with t ht
  simp only [nativeRealClockVolume,abs_of_neg ht]

theorem original_eh_cosmological_density_variation (κ Λ : ℝ) (G H : Tensor2)
    (negative : G.det < 0) :
    HasDerivAt (fun t : ℝ => originalEHCosmologicalMatrixDensity κ Λ (G + t • H))
      ((-Λ / κ) * ((1/2 : ℝ) * Real.sqrt (-G.det) * Matrix.trace (G⁻¹ * H))) 0 :=
  (original_eh_lorentz_volume_variation G H negative).const_mul (-Λ / κ)

end
end AASCSemanticExhaustion
