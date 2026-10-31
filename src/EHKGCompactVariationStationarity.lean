import EHKGScalarEulerLagrange

/-! Stationarity of the actual same-EH relative scalar action for every
compact smooth interior variation. The PDE is needed only on the diamond;
compact support supplies the true zero boundary flux outside that domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem same_eh_density_germ (a : Parameters) (F G : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (near : F =ᶠ[𝓝 p] G) : sameEHScalarDensity a F p = sameEHScalarDensity a G p := by
  have gradient : scalarPartial F p = scalarPartial G p := by
    funext i
    exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single i 1)) near.fderiv_eq
  simp only [sameEHScalarDensity, gradient, near.eq_of_nhds]

theorem off_support_zero_germ (d : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (outside : p ∉ tsupport d) : d =ᶠ[𝓝 p] (fun _ => 0) := by
  filter_upwards [(isClosed_tsupport (f := d)).isOpen_compl.mem_nhds outside] with q hq
  exact image_eq_zero_of_notMem_tsupport hq

theorem same_eh_zero_field_density (a : Parameters) (p : CoordinatePoint) :
    sameEHScalarDensity a (fun _ => 0) p = 0 := by
  simp [sameEHScalarDensity, nativeRealClockDensity, scalarPartial]

theorem variation_density_zero_off_tsupport (a : Parameters) (u d : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (outside : p ∉ tsupport d) : scalarFieldVariationDensity a u d p = 0 := by
  have nearD := off_support_zero_germ d p outside
  have nearSum : (fun q => u q + d q) =ᶠ[𝓝 p] u := nearD.mono (fun q hq => by simp [hq])
  rw [scalarFieldVariationDensity, same_eh_density_germ a _ u p nearSum,
    same_eh_density_germ a d (fun _ => 0) p nearD, same_eh_zero_field_density]
  ring

theorem variation_divergence_zero_off_tsupport (a : Parameters) (u d : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (outside : p ∉ tsupport d) : actualScalarVariationDivergence a u d p = 0 := by
  have nearD := off_support_zero_germ d p outside
  have partialZero (i : Fin 4) : scalarPartial (actualScalarVariationFlux a u d i) p i = 0 := by
    have nearFlux : actualScalarVariationFlux a u d i =ᶠ[𝓝 p] (fun _ => 0) :=
      nearD.mono (fun q hq => by simp [actualScalarVariationFlux, hq])
    have first := congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single i 1)) nearFlux.fderiv_eq
    simpa [scalarPartial] using first
  simp only [actualScalarVariationDivergence, partialZero, Finset.sum_const_zero]

theorem solved_variation_density_is_global_divergence (a : Parameters) (u : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u)
    (equation : ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p =
        (massWaveNumber a) ^ 2 * u p)
    (d : TestFunction ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ ℝ (⊤ : ℕ∞)) :
    scalarFieldVariationDensity a u d = actualScalarVariationDivergence a u d := by
  funext p
  by_cases hp : p ∈ protectedDiamond (conformalFrequency a)
  · rw [same_eh_scalar_euler_lagrange_identity a u d regularU d.contDiff p hp,
      equation p hp, sub_self, mul_zero, zero_mul, add_zero]
  · have outside : p ∉ tsupport d := fun h => hp (d.tsupport_subset h)
    rw [variation_density_zero_off_tsupport a u d p outside,
      variation_divergence_zero_off_tsupport a u d p outside]

theorem solved_variation_density_integral_zero (a : Parameters) (u : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u)
    (equation : ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p =
        (massWaveNumber a) ^ 2 * u p)
    (d : TestFunction ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ ℝ (⊤ : ℕ∞)) :
    (∫ p : CoordinatePoint, scalarFieldVariationDensity a u d p) = 0 := by
  rw [solved_variation_density_is_global_divergence a u regularU equation d]
  exact actual_scalar_variation_divergence_integral_zero a u d regularU d.contDiff d.hasCompactSupport

theorem action_linear_variation_is_integral (a : Parameters) (K : Compacts CoordinatePoint)
    (inside : (K : Set CoordinatePoint) ⊆ protectedDiamond (conformalFrequency a))
    (u d : CoordinatePoint → ℝ) (regularU : ContDiff ℝ (⊤ : ℕ∞) u)
    (regularD : ContDiff ℝ (⊤ : ℕ∞) d) :
    sameEHScalarActionLinearVariationOn a K u d =
      ∫ p in (K : Set CoordinatePoint), scalarFieldVariationDensity a u d p := by
  have iU : IntegrableOn (sameEHScalarDensity a u) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((same_eh_scalar_density_continuous a u regularU.contDiffOn).mono inside)
  have iD : IntegrableOn (sameEHScalarDensity a d) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((same_eh_scalar_density_continuous a d regularD.contDiffOn).mono inside)
  have iSum : IntegrableOn (sameEHScalarDensity a (fun q => u q + d q)) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((same_eh_scalar_density_continuous a _ (regularU.add regularD).contDiffOn).mono inside)
  unfold sameEHScalarActionLinearVariationOn sameEHScalarActionOn scalarFieldVariationDensity
  have split : (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a (fun q => u q + d q) p -
      sameEHScalarDensity a u p - sameEHScalarDensity a d p) =
      (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a (fun q => u q + d q) p - sameEHScalarDensity a u p) -
      ∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a d p := integral_sub (iSum.sub iU) iD
  rw [split, integral_sub iSum iU]

def sameEHRelativeFieldAction (a : Parameters) (u d : CoordinatePoint → ℝ) (s : ℝ) : ℝ :=
  ∫ p : CoordinatePoint, sameEHScalarDensity a (fun q => u q + s * d q) p - sameEHScalarDensity a u p

theorem relative_field_action_equals_compact_difference (a : Parameters) (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (K : Compacts CoordinatePoint) (inside : (K : Set CoordinatePoint) ⊆ protectedDiamond (conformalFrequency a))
    (supportD : tsupport d ⊆ (K : Set CoordinatePoint)) (s : ℝ) :
    sameEHRelativeFieldAction a u d s =
      sameEHScalarActionOn a K (fun q => u q + s * d q) - sameEHScalarActionOn a K u := by
  have regularPath : ContDiff ℝ (⊤ : ℕ∞) (fun q => u q + s * d q) :=
    regularU.add (contDiff_const.mul regularD)
  have iPath : IntegrableOn (sameEHScalarDensity a (fun q => u q + s * d q)) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((same_eh_scalar_density_continuous a _ regularPath.contDiffOn).mono inside)
  have iU : IntegrableOn (sameEHScalarDensity a u) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((same_eh_scalar_density_continuous a u regularU.contDiffOn).mono inside)
  have outsideZero (p : CoordinatePoint) (hp : p ∉ (K : Set CoordinatePoint)) :
      sameEHScalarDensity a (fun q => u q + s * d q) p - sameEHScalarDensity a u p = 0 := by
    have nearD := off_support_zero_germ d p (fun h => hp (supportD h))
    have nearPath : (fun q => u q + s * d q) =ᶠ[𝓝 p] u := nearD.mono (fun q hq => by simp [hq])
    rw [same_eh_density_germ a _ u p nearPath, sub_self]
  unfold sameEHRelativeFieldAction sameEHScalarActionOn
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero outsideZero]
  exact integral_sub iPath iU

theorem solved_same_eh_relative_field_action_stationary (a : Parameters) (u : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u)
    (equation : ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p =
        (massWaveNumber a) ^ 2 * u p)
    (d : TestFunction ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ ℝ (⊤ : ℕ∞)) :
    HasDerivAt (sameEHRelativeFieldAction a u d) 0 0 := by
  let K : Compacts CoordinatePoint := ⟨tsupport d, d.hasCompactSupport⟩
  have inside : (K : Set CoordinatePoint) ⊆ protectedDiamond (conformalFrequency a) := d.tsupport_subset
  have variationZero : sameEHScalarActionLinearVariationOn a K u d = 0 := by
    rw [action_linear_variation_is_integral a K inside u d regularU d.contDiff]
    change (∫ p in tsupport (d : CoordinatePoint → ℝ), scalarFieldVariationDensity a u d p) = 0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => variation_density_zero_off_tsupport a u d p hp)]
    exact solved_variation_density_integral_zero a u regularU equation d
  have derivative := (same_eh_scalar_action_field_hasDerivAt a K inside u d regularU d.contDiff).sub_const
    (sameEHScalarActionOn a K u)
  have functionEquality : sameEHRelativeFieldAction a u d =
      (fun s => sameEHScalarActionOn a K (fun q => u q + s * d q) - sameEHScalarActionOn a K u) := by
    funext s
    exact relative_field_action_equals_compact_difference a u d regularU d.contDiff K inside Subset.rfl s
  rw [functionEquality]
  simpa only [variationZero] using derivative

theorem compact_curved_field_stationary_for_all_compact_variations (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (d : TestFunction ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ ℝ (⊤ : ℕ∞)) :
    HasDerivAt (sameEHRelativeFieldAction a (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) d)
      0 0 :=
  solved_same_eh_relative_field_action_stationary a _ (compact_curved_field_smooth a _ f h)
    (fun p hp => compact_curved_field_equation a _ f h p (protected_diamond_subset_ball _ hp)) d

end AASCKleinGordon.CurvedKG
