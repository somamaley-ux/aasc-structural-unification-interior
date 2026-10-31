import KGWickCompactAction
import KGOriginalWickMetricCoefficient

/-! Actual fixed-action difference on the original quantum core. Compact
metric variations remove the need to integrate a global baseline action.
The Hilbert coefficient is a theorem about its ordinary derivative. -/
noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory Filter Set
open scoped Topology BigOperators
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem original_wick_derivative_components_continuous (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) : Continuous (originalWickDerivativeComponents a s u v) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (originalDerivativeWickMatrix_smooth a s u v _ _).continuous

theorem original_wick_mass_square_continuous (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) : Continuous (originalWickMassSquare a s u v) :=
  continuous_const.mul (originalWickSquareMatrix_smooth a s u v).continuous

def originalWickScalarRelativeAction (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (H : Spacetime → NativeRealMatrix) (t : ℝ) : ℂ :=
  ∫ x,wickQuantumActionDensity (wickFlatMetric+t • H x)
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x) -
    wickQuantumActionDensity wickFlatMetric
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)

def originalWickRaisedMetricPairing (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (H : Spacetime → NativeRealMatrix) : ℂ :=
  ∫ x,∑ i,∑ j,(H x i j : ℂ)*originalWickScalarStressRaisedMatrix a s u v i j x

theorem original_wick_scalar_action_metric_first_variation (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix)
    (hH : Continuous H) (hcomp : HasCompactSupport H)
    (hsym : ∀ x i j,H x i j=H x j i) :
    HasDerivAt (originalWickScalarRelativeAction a s u v H)
      ((1/2 : ℂ)*originalWickRaisedMetricPairing a s u v H) 0 := by
  let K : Set Spacetime := tsupport H
  have hK : IsCompact K := hcomp
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let m : Measure K := volume.comap (Subtype.val : K → Spacetime)
  letI : IsFiniteMeasure m := ⟨by
    change volume.comap (Subtype.val : K → Spacetime) univ < ⊤
    rw [comap_subtype_coe_apply hK.measurableSet,Set.image_univ,Subtype.range_coe]
    exact hK.measure_lt_top⟩
  have hD := original_wick_derivative_components_continuous a s u v
  have hM := original_wick_mass_square_continuous a s u v
  have hn : wickFlatMetric.det ≠ 0 := by rw [wick_flat_metric_det]; norm_num
  have hc := wick_compact_quantum_relative_action_hasDerivAt m
    (fun _ : K => wickFlatMetric) (fun p : K => H p)
    (fun p : K => originalWickDerivativeComponents a s u v p)
    (fun p : K => originalWickMassSquare a s u v p)
    continuous_const (hH.comp continuous_subtype_val)
    (hD.comp continuous_subtype_val) (hM.comp continuous_subtype_val) (fun _ => hn)
  have hzero (x : Spacetime) (hx : x ∉ K) : H x=0 := image_eq_zero_of_notMem_tsupport hx
  have hfun (t : ℝ) : (∫ x : K,wickQuantumActionDensity (wickFlatMetric+t • H x)
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
      wickQuantumActionDensity wickFlatMetric
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x) ∂m) =
      originalWickScalarRelativeAction a s u v H t := by
    dsimp only [m]
    rw [integral_subtype_comap hK.measurableSet (fun x : Spacetime =>
      wickQuantumActionDensity (wickFlatMetric+t • H x)
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
      wickQuantumActionDensity wickFlatMetric
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x))]
    unfold originalWickScalarRelativeAction
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      by_cases hx : x ∈ K
      · simp [hx]
      · simp [hx,hzero x hx])
  have hout : (∫ x : K,wickQuantumDensityVariation wickFlatMetric (H x)
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x) ∂m) =
      (1/2 : ℂ)*originalWickRaisedMetricPairing a s u v H := by
    dsimp only [m]
    rw [integral_subtype_comap hK.measurableSet (fun x : Spacetime =>
      wickQuantumDensityVariation wickFlatMetric (H x)
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x))]
    have hrestrict : (∫ x in K,wickQuantumDensityVariation wickFlatMetric (H x)
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)) =
        ∫ x,wickQuantumDensityVariation wickFlatMetric (H x)
          (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x) := by
      rw [← integral_indicator hK.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        by_cases hx : x ∈ K
        · simp [hx]
        · simp [hx,hzero x hx,wickQuantumDensityVariation])
    rw [hrestrict]
    simp_rw [original_wick_metric_density_coefficient a s u v _ (hsym _) _]
    rw [integral_const_mul]
    rfl
  convert hc using 1
  · funext t
    exact (hfun t).symm
  · exact hout.symm

end AASCKleinGordon
