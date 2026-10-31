import KGFlatLocalBalance

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace AASCKleinGordon

def flatEnergyDensity (μ : ℝ) (u v : ℝ → KGSpatialSpace → ℝ)
    (w : ℝ → KGSpatialSpace → KGSpatialSpace) (t : ℝ) (x : KGSpatialSpace) : ℝ :=
  flatKGEnergy μ (u t x) (v t x) (w t x)

def flatEnergyFlux (v : ℝ → KGSpatialSpace → ℝ)
    (w : ℝ → KGSpatialSpace → KGSpatialSpace) (t : ℝ) (x : KGSpatialSpace) : KGSpatialSpace :=
  flatKGFlux (v t x) (w t x)

def localizedKGEnergy (δ R μ : ℝ) (x₀ : KGSpatialSpace)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace) (t : ℝ) : ℝ :=
  ∫ x, smoothConeCutoff δ R t x₀ x*flatEnergyDensity μ u v w t x

def localizedKGEnergyRate (δ R μ : ℝ) (x₀ : KGSpatialSpace)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace) (t : ℝ) : ℝ :=
  ∫ x, smoothConeCutoffTimeDerivative δ R t x₀ x*flatEnergyDensity μ u v w t x-
    inner ℝ (smoothConeCutoffGradient δ R t x₀ x) (flatEnergyFlux v w t x)

theorem flatEnergyDensity_joint_continuous
    (μ : ℝ) (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (hu : Continuous (Function.uncurry u)) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w)) :
    Continuous (Function.uncurry (flatEnergyDensity μ u v w)) :=
  (((hv.pow 2).add (hw.norm.pow 2)).add (continuous_const.mul (hu.pow 2))).div_const 2

theorem flatEnergyFlux_joint_continuous
    (v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (hv : Continuous (Function.uncurry v)) (hw : Continuous (Function.uncurry w)) :
    Continuous (Function.uncurry (flatEnergyFlux v w)) := hv.smul hw

theorem localizedKGEnergyRate_nonpos (δ R μ t : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace) :
    localizedKGEnergyRate δ R μ x₀ u v w t ≤ 0 := by
  apply integral_nonpos_of_ae
  exact Filter.Eventually.of_forall fun x =>
    flatKG_weighted_energy_rate_nonpos μ (u t x) (v t x)
      (smoothConeCutoffTimeDerivative δ R t x₀ x) (w t x)
      (smoothConeCutoffGradient δ R t x₀ x) (smoothConeCutoff_energy_sign δ R t x₀ x hδ)

/-- Local energy differentiation and spatial integration by parts are proved here.
The explicit local derivative identity is discharged by `flatKG_local_energy_balance`
for first-order KG solutions; it is not an assumed finite-propagation conclusion. -/
theorem localizedKGEnergy_hasDerivAt
    (δ R μ : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace)
    (hu : Continuous (Function.uncurry u)) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w))
    (hdiv : Continuous (fun z : ℝ × KGSpatialSpace => kgSpatialDivergence (flatEnergyFlux v w z.1) z.2))
    (hJd : ∀ t, ∀ i : Fin 3, Differentiable ℝ (fun x => flatEnergyFlux v w t x i))
    (hDJ : ∀ t, ∀ i : Fin 3, Continuous
      (fun x => fderiv ℝ (fun y => flatEnergyFlux v w t y i) x (kgSpatialDirection i)))
    (hbalance : ∀ t x, HasDerivAt (fun s => flatEnergyDensity μ u v w s x)
      (kgSpatialDivergence (flatEnergyFlux v w t) x) t)
    (t : ℝ) :
    HasDerivAt (localizedKGEnergy δ R μ x₀ u v w)
      (localizedKGEnergyRate δ R μ x₀ u v w t) t := by
  let e := flatEnergyDensity μ u v w
  let J := flatEnergyFlux v w
  let F := fun s x => smoothConeCutoff δ R s x₀ x*e s x
  let F' := fun s x => smoothConeCutoffTimeDerivative δ R s x₀ x*e s x+
    smoothConeCutoff δ R s x₀ x*kgSpatialDivergence (J s) x
  have he := flatEnergyDensity_joint_continuous μ u v w hu hv hw
  have hj := flatEnergyFlux_joint_continuous v w hv hw
  have hc := (smoothConeCutoff_joint_contDiff δ R x₀ hδ).continuous
  have hct := smoothConeCutoffTimeDerivative_joint_continuous δ R x₀ hδ
  have hF : Continuous (Function.uncurry F) := hc.mul he
  have hF' : Continuous (Function.uncurry F') := (hct.mul he).add (hc.mul hdiv)
  have hh := compactIntegral_hasDerivAt volume F F' t (Metric.closedBall x₀ (R-(t-1)))
    (isCompact_closedBall x₀ (R-(t-1))) hF hF' (by
      intro s hs x hx
      obtain ⟨h1,h2,h3⟩ := smoothConeCutoff_uniform_support δ R (t-1) (t+1) s x₀ x hs hx
      simp [F,F',h1,h2]) (by
      intro x s hs
      exact (smoothConeCutoff_hasDerivAt δ R s x₀ x).mul (hbalance s x))
  have hs : Continuous (fun x => e t x) := he.comp (continuous_const.prodMk continuous_id)
  have hjs : Continuous (J t) := hj.comp (continuous_const.prodMk continuous_id)
  have hcs : Continuous (smoothConeCutoff δ R t x₀) := hc.comp (continuous_const.prodMk continuous_id)
  have hcts : Continuous (smoothConeCutoffTimeDerivative δ R t x₀) := hct.comp (continuous_const.prodMk continuous_id)
  have hgs : Continuous (smoothConeCutoffGradient δ R t x₀) :=
    (smoothConeCutoffGradient_joint_continuous δ R x₀ hδ).comp (continuous_const.prodMk continuous_id)
  have hds : Continuous (fun x => kgSpatialDivergence (J t) x) :=
    hdiv.comp (continuous_const.prodMk continuous_id)
  have h1 : Integrable (fun x => smoothConeCutoffTimeDerivative δ R t x₀ x*e t x) :=
    (hcts.mul hs).integrable_of_hasCompactSupport
      (smoothConeCutoffTimeDerivative_hasCompactSupport δ R t x₀).mul_right
  have h2 : Integrable (fun x => smoothConeCutoff δ R t x₀ x*kgSpatialDivergence (J t) x) :=
    (hcs.mul hds).integrable_of_hasCompactSupport
      (smoothConeCutoff_hasCompactSupport δ R t x₀).mul_right
  have h3 : Integrable (fun x => inner ℝ (smoothConeCutoffGradient δ R t x₀ x) (J t x)) := by
    apply (hgs.inner hjs).integrable_of_hasCompactSupport
    apply compactSupport_of_zero_outside_compact (isCompact_closedBall x₀ (R-t))
    intro x hx
    rw [(smoothConeCutoff_uniform_support δ R t t t x₀ x ⟨le_rfl,le_rfl⟩ hx).2.2]
    simp
  convert hh using 1
  unfold localizedKGEnergyRate F'
  rw [integral_add h1 h2,integral_sub h1 h3,
    smoothConeCutoff_integral_divergence δ R t x₀ hδ (J t) hjs (hJd t) (hDJ t)]
  ring

theorem localizedKGEnergy_nonneg (δ R μ t : ℝ) (x₀ : KGSpatialSpace)
    (u v : ℝ → KGSpatialSpace → ℝ) (w : ℝ → KGSpatialSpace → KGSpatialSpace) :
    0 ≤ localizedKGEnergy δ R μ x₀ u v w t :=
  integral_nonneg (fun x => mul_nonneg (smoothConeCutoff_nonneg δ R t x₀ x)
    (flatKGEnergy_nonneg μ (u t x) (v t x) (w t x)))

end AASCKleinGordon
