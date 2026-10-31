import CompactMetricSourceRepresentation
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Construct regular-density distributions and their LF-continuous metric
functional directly by integration, using only local integrability on Ω. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open TopologicalSpace MeasureTheory Filter Set
open scoped BigOperators Topology BoundedContinuousFunction

abbrev NativeSourcePoint:=Fin 4 → ℝ

variable {ρ : NativeSourcePoint → ℝ}

theorem native_integrable_density_times_bounded (hρ : Integrable ρ volume)
    (f : NativeSourcePoint →ᵇ ℝ) : Integrable (fun p => ρ p*f p) volume :=
  hρ.mul_bdd f.continuous.aestronglyMeasurable (Eventually.of_forall f.norm_coe_le_norm)

def nativeWeightedBoundedLinear (ρ : NativeSourcePoint → ℝ) (hρ : Integrable ρ volume) :
    (NativeSourcePoint →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun f:=∫ p,ρ p*f p
  map_add' f g:=by
    simp only [BoundedContinuousFunction.add_apply,mul_add]
    exact integral_add (native_integrable_density_times_bounded hρ f)
      (native_integrable_density_times_bounded hρ g)
  map_smul' r f:=by
    simp only [BoundedContinuousFunction.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm (ρ _) r,mul_assoc]
    exact integral_const_mul r _

def nativeWeightedBoundedCLM (ρ : NativeSourcePoint → ℝ) (hρ : Integrable ρ volume) :
    (NativeSourcePoint →ᵇ ℝ) →L[ℝ] ℝ :=
  (nativeWeightedBoundedLinear ρ hρ).mkContinuous (∫ p,‖ρ p‖) (by
    intro f
    change ‖∫ p,ρ p*f p‖≤(∫ p,‖ρ p‖)*‖f‖
    calc
      _≤∫ p,‖ρ p*f p‖:=norm_integral_le_integral_norm _
      _≤∫ p,‖ρ p‖*‖f‖:=by
        apply integral_mono (native_integrable_density_times_bounded hρ f).norm (hρ.norm.mul_const ‖f‖)
        intro p
        change ‖ρ p*f p‖≤‖ρ p‖*‖f‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm p) (norm_nonneg _)
      _=(∫ p,‖ρ p‖)*‖f‖:=integral_mul_const _ _)

variable {Ω : Opens NativeSourcePoint}

theorem native_locally_integrable_test_product
    (ρ : NativeSourcePoint → ℝ) (hρ : LocallyIntegrableOn ρ (Ω:Set NativeSourcePoint) volume)
    (f : ScalarSourceProbe Ω) : Integrable (fun p => ρ p*f p) volume := by
  let K:Set NativeSourcePoint:=tsupport f
  have hK:IsCompact K:=f.hasCompactSupport
  have hi:IntegrableOn ρ K volume:=hρ.integrableOn_compact_subset f.tsupport_subset hK
  have hind:Integrable (K.indicator ρ) volume:=(integrable_indicator_iff hK.measurableSet).2 hi
  have hp:=native_integrable_density_times_bounded hind (TestFunction.toBoundedContinuousFunctionCLM ℝ f)
  convert hp using 1
  funext p
  by_cases hk:p∈K
  · simp [hk]
  · simp [hk,image_eq_zero_of_notMem_tsupport hk]

def nativeRegularScalarDensity (ρ : NativeSourcePoint → ℝ)
    (hρ : LocallyIntegrableOn ρ (Ω:Set NativeSourcePoint) volume) : ScalarSourceProbe Ω →L[ℝ] ℝ :=
  TestFunction.mkCLM ℝ (fun f => ∫ p,ρ p*f p)
    (by intro f g
        change (∫ p,ρ p*(f p+g p))=(∫ p,ρ p*f p)+(∫ p,ρ p*g p)
        simp only [mul_add]
        exact integral_add (native_locally_integrable_test_product ρ hρ f)
          (native_locally_integrable_test_product ρ hρ g))
    (by intro r f
        change (∫ p,ρ p*(r*f p))=r*(∫ p,ρ p*f p)
        simp_rw [← mul_assoc,mul_comm (ρ _) r,mul_assoc]
        exact integral_const_mul r _)
    (by
      intro K hK
      have hi:IntegrableOn ρ (K:Set NativeSourcePoint) volume:=
        hρ.integrableOn_compact_subset hK K.isCompact
      have hind:Integrable ((K:Set NativeSourcePoint).indicator ρ) volume:=
        (integrable_indicator_iff K.isCompact.measurableSet).2 hi
      have heq : (fun f : ContDiffMapSupportedIn NativeSourcePoint ℝ (⊤:ℕ∞) K => ∫ p,ρ p*(TestFunction.ofSupportedIn hK f) p)=
          fun f => nativeWeightedBoundedCLM ((K:Set NativeSourcePoint).indicator ρ) hind
            (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ f) := by
        funext f
        change (∫ p,ρ p*f p)=∫ p,(K:Set NativeSourcePoint).indicator ρ p*f p
        apply integral_congr_ae
        apply Eventually.of_forall
        intro p
        by_cases hp:p∈K
        · simp [hp]
        · have hz:=f.zero_on_compl hp
          simp [hp,hz]
      change Continuous (fun f => ∫ p,ρ p*(TestFunction.ofSupportedIn hK f) p)
      rw [heq]
      exact (nativeWeightedBoundedCLM _ hind).continuous.comp
        (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ).continuous)

def nativeRegularMetricDensity (ρ : Fin 10 → NativeSourcePoint → ℝ)
    (hρ : ∀ i,LocallyIntegrableOn (ρ i) (Ω:Set NativeSourcePoint) volume) :
    MetricSourceProbe Ω →L[ℝ] ℝ :=
  ∑ i,(symmetricSourceWeight i/2) • (nativeRegularScalarDensity (ρ i) (hρ i)).comp (sourceTestProjection i)

theorem native_regular_metric_density_integral (ρ : Fin 10 → NativeSourcePoint → ℝ)
    (hρ : ∀ i,LocallyIntegrableOn (ρ i) (Ω:Set NativeSourcePoint) volume) (h : MetricSourceProbe Ω) :
    nativeRegularMetricDensity ρ hρ h=
      ∑ i,(symmetricSourceWeight i/2)*(∫ p,ρ i p*h p i) := by
  simp [nativeRegularMetricDensity,nativeRegularScalarDensity,sourceTestProjection,
    TestFunction.postcompCLM_apply,ContinuousLinearMap.sum_apply]

#print axioms native_integrable_density_times_bounded
#print axioms native_locally_integrable_test_product
#print axioms native_regular_metric_density_integral
end
end AASCSemanticExhaustion
