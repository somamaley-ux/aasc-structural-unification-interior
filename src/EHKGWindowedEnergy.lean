import EHKGCompactSmoothLocalization
import KGFlatFinitePropagation

/-! A finite-window version of the retained energy argument. The actual
energy derivative may differ from flux divergence outside the shrinking cone;
only their cutoff-weighted identity is needed. No local uniqueness conclusion
or desired propagator is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def localizedActualEnergyRate (delta R mu : ℝ) (center : KGSpatialSpace)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (G : ℝ → KGSpatialSpace → ℝ) (t : ℝ) : ℝ :=
  ∫ x, smoothConeCutoffTimeDerivative delta R t center x * flatEnergyDensity mu u v w t x +
    smoothConeCutoff delta R t center x * G t x

theorem localized_energy_actual_hasDerivAt (delta R mu : ℝ) (center : KGSpatialSpace)
    (positive : 0 < delta)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (G : ℝ → KGSpatialSpace → ℝ)
    (hu : Continuous (Function.uncurry u)) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w)) (hG : Continuous (Function.uncurry G))
    (energyDerivative : ∀ t x, HasDerivAt (fun s => flatEnergyDensity mu u v w s x) (G t x) t)
    (t : ℝ) :
    HasDerivAt (localizedKGEnergy delta R mu center u v w)
      (localizedActualEnergyRate delta R mu center u v w G t) t := by
  let F := fun s x => smoothConeCutoff delta R s center x * flatEnergyDensity mu u v w s x
  let F' := fun s x => smoothConeCutoffTimeDerivative delta R s center x * flatEnergyDensity mu u v w s x +
    smoothConeCutoff delta R s center x * G s x
  have energyContinuous := flatEnergyDensity_joint_continuous mu u v w hu hv hw
  have cutoffContinuous := (smoothConeCutoff_joint_contDiff delta R center positive).continuous
  have derivativeContinuous := smoothConeCutoffTimeDerivative_joint_continuous delta R center positive
  exact compactIntegral_hasDerivAt volume F F' t (Metric.closedBall center (R - (t - 1)))
    (isCompact_closedBall _ _) (cutoffContinuous.mul energyContinuous)
    ((derivativeContinuous.mul energyContinuous).add (cutoffContinuous.mul hG)) (by
      intro s hs x hx
      obtain ⟨zero, derivativeZero, gradientZero⟩ :=
        smoothConeCutoff_uniform_support delta R (t - 1) (t + 1) s center x hs hx
      simp [F, F', zero, derivativeZero]) (by
      intro x s hs
      exact (smoothConeCutoff_hasDerivAt delta R s center x).mul (energyDerivative s x))

theorem localized_actual_rate_eq_energy_rate (delta R mu t : ℝ) (center : KGSpatialSpace)
    (positive : 0 < delta)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (G : ℝ → KGSpatialSpace → ℝ)
    (hu : Continuous (Function.uncurry u)) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w))
    (hdiv : Continuous (fun z : ℝ × KGSpatialSpace => kgSpatialDivergence (flatEnergyFlux v w z.1) z.2))
    (fluxSpatial : ∀ i : Fin 3, Differentiable ℝ (fun x => flatEnergyFlux v w t x i))
    (fluxDerivative : ∀ i : Fin 3, Continuous
      (fun x => fderiv ℝ (fun y => flatEnergyFlux v w t y i) x (kgSpatialDirection i)))
    (weighted : ∀ x, smoothConeCutoff delta R t center x * G t x =
      smoothConeCutoff delta R t center x * kgSpatialDivergence (flatEnergyFlux v w t) x) :
    localizedActualEnergyRate delta R mu center u v w G t = localizedKGEnergyRate delta R mu center u v w t := by
  let e := flatEnergyDensity mu u v w
  let J := flatEnergyFlux v w
  have energyContinuous := flatEnergyDensity_joint_continuous mu u v w hu hv hw
  have fluxContinuous := flatEnergyFlux_joint_continuous v w hv hw
  have cutoffContinuous := (smoothConeCutoff_joint_contDiff delta R center positive).continuous
  have cutoffTimeContinuous := smoothConeCutoffTimeDerivative_joint_continuous delta R center positive
  have cutoffGradientContinuous := smoothConeCutoffGradient_joint_continuous delta R center positive
  have first : Integrable (fun x => smoothConeCutoffTimeDerivative delta R t center x * e t x) :=
    ((cutoffTimeContinuous.mul energyContinuous).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (smoothConeCutoffTimeDerivative_hasCompactSupport delta R t center).mul_right
  have second : Integrable (fun x => smoothConeCutoff delta R t center x * kgSpatialDivergence (J t) x) :=
    ((cutoffContinuous.mul hdiv).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (smoothConeCutoff_hasCompactSupport delta R t center).mul_right
  have third : Integrable (fun x => inner ℝ (smoothConeCutoffGradient delta R t center x) (J t x)) := by
    apply ((cutoffGradientContinuous.inner fluxContinuous).comp
      (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply compactSupport_of_zero_outside_compact (isCompact_closedBall center (R - t))
    intro x hx
    rw [(smoothConeCutoff_uniform_support delta R t t t center x ⟨le_rfl, le_rfl⟩ hx).2.2]
    simp
  unfold localizedActualEnergyRate
  simp_rw [weighted]
  rw [integral_add first second, localizedKGEnergyRate, integral_sub first third,
    smoothConeCutoff_integral_divergence delta R t center positive (J t)
      (fluxContinuous.comp (continuous_const.prodMk continuous_id)) fluxSpatial fluxDerivative]
  ring

theorem localized_energy_antitoneOn_window (delta R mu T : ℝ) (center : KGSpatialSpace)
    (positive : 0 < delta)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (G : ℝ → KGSpatialSpace → ℝ)
    (hu : Continuous (Function.uncurry u)) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w)) (hG : Continuous (Function.uncurry G))
    (energyDerivative : ∀ t x, HasDerivAt (fun s => flatEnergyDensity mu u v w s x) (G t x) t)
    (hdiv : Continuous (fun z : ℝ × KGSpatialSpace => kgSpatialDivergence (flatEnergyFlux v w z.1) z.2))
    (fluxSpatial : ∀ t, ∀ i : Fin 3, Differentiable ℝ (fun x => flatEnergyFlux v w t x i))
    (fluxDerivative : ∀ t, ∀ i : Fin 3, Continuous
      (fun x => fderiv ℝ (fun y => flatEnergyFlux v w t y i) x (kgSpatialDirection i)))
    (weighted : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, smoothConeCutoff delta R t center x * G t x =
      smoothConeCutoff delta R t center x * kgSpatialDivergence (flatEnergyFlux v w t) x) :
    AntitoneOn (localizedKGEnergy delta R mu center u v w) (Icc 0 T) := by
  have actual := localized_energy_actual_hasDerivAt delta R mu center positive u v w G hu hv hw hG energyDerivative
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    (fun t _ => (actual t).continuousAt.continuousWithinAt)
  · intro t ht
    exact (actual t).hasDerivWithinAt
  · intro t ht
    rw [localized_actual_rate_eq_energy_rate delta R mu t center positive u v w G hu hv hw hdiv
      (fluxSpatial t) (fluxDerivative t) (weighted t (by simpa only [interior_Icc] using ht))]
    exact localizedKGEnergyRate_nonpos delta R mu t center positive u v w

theorem localized_window_vanishes (R mu T : ℝ) (center : KGSpatialSpace)
    (mass : mu ≠ 0) (time : 0 ≤ T) (radius : T < R)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (G : ℝ → KGSpatialSpace → ℝ)
    (hu : Continuous (Function.uncurry u)) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w)) (hG : Continuous (Function.uncurry G))
    (energyDerivative : ∀ t x, HasDerivAt (fun s => flatEnergyDensity mu u v w s x) (G t x) t)
    (hdiv : Continuous (fun z : ℝ × KGSpatialSpace => kgSpatialDivergence (flatEnergyFlux v w z.1) z.2))
    (fluxSpatial : ∀ t, ∀ i : Fin 3, Differentiable ℝ (fun x => flatEnergyFlux v w t x i))
    (fluxDerivative : ∀ t, ∀ i : Fin 3, Continuous
      (fun x => fderiv ℝ (fun y => flatEnergyFlux v w t y i) x (kgSpatialDirection i)))
    (balanceWindow : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Metric.closedBall center (R - t),
      G t x = kgSpatialDivergence (flatEnergyFlux v w t) x)
    (initial : ∀ x ∈ Metric.closedBall center R, u 0 x = 0 ∧ v 0 x = 0 ∧ w 0 x = 0) :
    u T center = 0 := by
  let delta := (R - T) / 2
  have positive : 0 < delta := by dsimp [delta]; linarith
  have margin : T + delta < R := by dsimp [delta]; linarith
  have weighted (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (x : KGSpatialSpace) :
      smoothConeCutoff delta R t center x * G t x =
        smoothConeCutoff delta R t center x * kgSpatialDivergence (flatEnergyFlux v w t) x := by
    by_cases hx : x ∈ Metric.closedBall center (R - t)
    · rw [balanceWindow t ht x hx]
    · rw [(smoothConeCutoff_uniform_support delta R t t t center x ⟨le_rfl, le_rfl⟩ hx).1]
      simp only [zero_mul]
  have anti := localized_energy_antitoneOn_window delta R mu T center positive u v w G hu hv hw hG
    energyDerivative hdiv fluxSpatial fluxDerivative weighted
  have initialEnergy : localizedKGEnergy delta R mu center u v w 0 = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ Metric.closedBall center R
      · obtain ⟨zeroU, zeroV, zeroW⟩ := initial x hx
        simp [flatEnergyDensity, flatKGEnergy, zeroU, zeroV, zeroW]
      · have cutoffZero := (smoothConeCutoff_uniform_support delta R 0 0 0 center x
          ⟨le_rfl, le_rfl⟩ (by simpa using hx)).1
        simp [cutoffZero]
  have terminalEnergy : localizedKGEnergy delta R mu center u v w T = 0 := by
    apply le_antisymm
    · simpa only [initialEnergy] using anti (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, time⟩)
        (show T ∈ Icc 0 T from ⟨time, le_rfl⟩) time
    · exact localizedKGEnergy_nonneg delta R mu T center u v w
  by_contra nonzero
  have energyNonzero : flatEnergyDensity mu u v w T center ≠ 0 := by
    intro zero
    exact nonzero ((flatKGEnergy_eq_zero_iff mu (u T center) (v T center) (w T center) mass).mp zero).1
  have cutoffPositive := smoothConeCutoff_pos_at_center delta R T center positive margin
  have energyContinuous := flatEnergyDensity_joint_continuous mu u v w hu hv hw
  have cutoffContinuous := (smoothConeCutoff_joint_contDiff delta R center positive).continuous
  have integrandContinuous : Continuous
      (fun x => smoothConeCutoff delta R T center x * flatEnergyDensity mu u v w T x) :=
    (cutoffContinuous.mul energyContinuous).comp (continuous_const.prodMk continuous_id)
  have integrable : Integrable (fun x => smoothConeCutoff delta R T center x * flatEnergyDensity mu u v w T x) := integrandContinuous.integrable_of_hasCompactSupport
    (smoothConeCutoff_hasCompactSupport delta R T center).mul_right
  have energyPositive : 0 < localizedKGEnergy delta R mu center u v w T :=
    integral_pos_of_integrable_nonneg_nonzero integrandContinuous integrable
      (fun x => mul_nonneg (smoothConeCutoff_nonneg delta R T center x)
        (flatKGEnergy_nonneg mu (u T x) (v T x) (w T x)))
      (mul_ne_zero (ne_of_gt cutoffPositive) energyNonzero)
  linarith

end AASCKleinGordon.CurvedKG
