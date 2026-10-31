import KGLocalizedEnergyDecay

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace AASCKleinGordon

/-- Explicit regularity and first-order differential equations for the local energy
theorem. No support conclusion, causal propagator, or distributional bridge is a field.
The concrete Fourier sine solution has still to be attached to these hypotheses. -/
structure FlatKGFirstOrderSolution (μ : ℝ) where
  u : ℝ → KGSpatialSpace → ℝ
  v : ℝ → KGSpatialSpace → ℝ
  w : ℝ → KGSpatialSpace → KGSpatialSpace
  gradientV : ℝ → KGSpatialSpace → KGSpatialSpace
  continuousU : Continuous (Function.uncurry u)
  continuousV : Continuous (Function.uncurry v)
  continuousW : Continuous (Function.uncurry w)
  spatialV : ∀ t, Differentiable ℝ (v t)
  spatialW : ∀ t, ∀ i : Fin 3, Differentiable ℝ (fun x => w t x i)
  gradientV_eq : ∀ t x, ∀ i : Fin 3, fderiv ℝ (v t) x (kgSpatialDirection i)=gradientV t x i
  timeU : ∀ t x, HasDerivAt (fun s => u s x) (v t x) t
  timeV : ∀ t x, HasDerivAt (fun s => v s x) (kgSpatialDivergence (w t) x-μ^2*u t x) t
  timeW : ∀ t x, HasDerivAt (fun s => w s x) (gradientV t x) t
  divergenceContinuous : Continuous
    (fun z : ℝ × KGSpatialSpace => kgSpatialDivergence (flatEnergyFlux v w z.1) z.2)
  fluxSpatial : ∀ t, ∀ i : Fin 3, Differentiable ℝ (fun x => flatEnergyFlux v w t x i)
  fluxDerivativeContinuous : ∀ t, ∀ i : Fin 3, Continuous
    (fun x => fderiv ℝ (fun y => flatEnergyFlux v w t y i) x (kgSpatialDirection i))

theorem FlatKGFirstOrderSolution.energy_balance {μ : ℝ} (s : FlatKGFirstOrderSolution μ)
    (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun r => flatEnergyDensity μ s.u s.v s.w r x)
      (kgSpatialDivergence (flatEnergyFlux s.v s.w t) x) t :=
  flatKG_local_energy_balance μ s.u s.v s.w t x (s.gradientV t x)
    (s.spatialV t) (s.spatialW t) (s.gradientV_eq t x) (s.timeU t x) (s.timeV t x) (s.timeW t x)

theorem FlatKGFirstOrderSolution.localized_energy_hasDerivAt
    {μ : ℝ} (s : FlatKGFirstOrderSolution μ) (δ R t : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ) :
    HasDerivAt (localizedKGEnergy δ R μ x₀ s.u s.v s.w)
      (localizedKGEnergyRate δ R μ x₀ s.u s.v s.w t) t :=
  localizedKGEnergy_hasDerivAt δ R μ x₀ hδ s.u s.v s.w
    s.continuousU s.continuousV s.continuousW s.divergenceContinuous
    s.fluxSpatial s.fluxDerivativeContinuous s.energy_balance t

theorem FlatKGFirstOrderSolution.localized_energy_antitone
    {μ : ℝ} (s : FlatKGFirstOrderSolution μ) (δ R : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ) :
    Antitone (localizedKGEnergy δ R μ x₀ s.u s.v s.w) :=
  antitone_of_hasDerivAt_nonpos (fun t => s.localized_energy_hasDerivAt δ R t x₀ hδ)
    (fun t => localizedKGEnergyRate_nonpos δ R μ t x₀ hδ s.u s.v s.w)

/-- Forward domain of dependence for the explicitly stated homogeneous first-order
KG equations. A smooth compact shrinking cutoff proves this without a cutoff limit. -/
theorem FlatKGFirstOrderSolution.vanishes_inside_forward_cone
    {μ : ℝ} (s : FlatKGFirstOrderSolution μ) (hμ : μ ≠ 0)
    (R t : ℝ) (x₀ : KGSpatialSpace) (ht : 0 ≤ t) (hRt : t < R)
    (hinitial : ∀ x ∈ Metric.closedBall x₀ R, s.u 0 x=0 ∧ s.v 0 x=0 ∧ s.w 0 x=0) :
    s.u t x₀=0 := by
  let δ := (R-t)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hRδ : t+δ < R := by dsimp [δ]; linarith
  have hzero : localizedKGEnergy δ R μ x₀ s.u s.v s.w 0=0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ Metric.closedBall x₀ R
      · obtain ⟨hu,hv,hw⟩ := hinitial x hx
        simp [flatEnergyDensity,flatKGEnergy,hu,hv,hw]
      · have hc := (smoothConeCutoff_uniform_support δ R 0 0 0 x₀ x ⟨le_rfl,le_rfl⟩ (by simpa using hx)).1
        simp [hc]
  have hterminal : localizedKGEnergy δ R μ x₀ s.u s.v s.w t=0 := by
    apply le_antisymm
    · simpa only [hzero] using s.localized_energy_antitone δ R x₀ hδ ht
    · exact localizedKGEnergy_nonneg δ R μ t x₀ s.u s.v s.w
  by_contra hne
  have hene : flatEnergyDensity μ s.u s.v s.w t x₀ ≠ 0 := by
    intro he
    exact hne ((flatKGEnergy_eq_zero_iff μ (s.u t x₀) (s.v t x₀) (s.w t x₀) hμ).mp he).1
  have hcpos := smoothConeCutoff_pos_at_center δ R t x₀ hδ hRδ
  have hec := flatEnergyDensity_joint_continuous μ s.u s.v s.w s.continuousU s.continuousV s.continuousW
  have hcc := (smoothConeCutoff_joint_contDiff δ R x₀ hδ).continuous
  have hcont : Continuous (fun x => smoothConeCutoff δ R t x₀ x*flatEnergyDensity μ s.u s.v s.w t x) :=
    (hcc.mul hec).comp (continuous_const.prodMk continuous_id)
  have hint : Integrable (fun x => smoothConeCutoff δ R t x₀ x*flatEnergyDensity μ s.u s.v s.w t x) :=
    hcont.integrable_of_hasCompactSupport (smoothConeCutoff_hasCompactSupport δ R t x₀).mul_right
  have hpos : 0 < localizedKGEnergy δ R μ x₀ s.u s.v s.w t :=
    integral_pos_of_integrable_nonneg_nonzero hcont hint
      (fun x => mul_nonneg (smoothConeCutoff_nonneg δ R t x₀ x)
        (flatKGEnergy_nonneg μ (s.u t x) (s.v t x) (s.w t x)))
      (mul_ne_zero (ne_of_gt hcpos) hene)
  linarith

end AASCKleinGordon
