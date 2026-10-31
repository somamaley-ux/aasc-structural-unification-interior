import EHKGCompactVariationStationarity

/-! The global relative-action integral is genuinely integrable. The
unvaried action need not have a finite integral over the entire carrier. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem same_eh_relative_field_action_integrable (a : Parameters) (u : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u)
    (d : TestFunction ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ ℝ (⊤ : ℕ∞))
    (s : ℝ) :
    Integrable (fun p : CoordinatePoint =>
      sameEHScalarDensity a (fun q => u q + s * d q) p - sameEHScalarDensity a u p) := by
  let K : Set CoordinatePoint := tsupport d
  let difference : CoordinatePoint → ℝ := fun p =>
    sameEHScalarDensity a (fun q => u q + s * d q) p - sameEHScalarDensity a u p
  have regularPath : ContDiff ℝ (⊤ : ℕ∞) (fun q => u q + s * d q) :=
    regularU.add (contDiff_const.mul d.contDiff)
  have iPath : IntegrableOn (sameEHScalarDensity a (fun q => u q + s * d q)) K :=
    ContinuousOn.integrableOn_compact d.hasCompactSupport
      ((same_eh_scalar_density_continuous a _ regularPath.contDiffOn).mono d.tsupport_subset)
  have iU : IntegrableOn (sameEHScalarDensity a u) K :=
    ContinuousOn.integrableOn_compact d.hasCompactSupport
      ((same_eh_scalar_density_continuous a u regularU.contDiffOn).mono d.tsupport_subset)
  have supportInside : Function.support difference ⊆ K := by
    intro p hp
    by_contra outside
    have nearD := off_support_zero_germ d p outside
    have nearPath : (fun q => u q + s * d q) =ᶠ[𝓝 p] u := nearD.mono (fun q hq => by simp [hq])
    apply hp
    exact sub_eq_zero.mpr (same_eh_density_germ a _ u p nearPath)
  have indicatorIntegrable : Integrable (K.indicator difference) :=
    (integrable_indicator_iff d.hasCompactSupport.measurableSet).mpr (iPath.sub iU)
  rw [indicator_eq_self.mpr supportInside] at indicatorIntegrable
  exact indicatorIntegrable

theorem compact_curved_same_action_variation_endpoint (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (d : TestFunction ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ ℝ (⊤ : ℕ∞)) :
    (∀ s : ℝ, Integrable (fun p : CoordinatePoint =>
      sameEHScalarDensity a (fun q => compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h q + s * d q) p -
      sameEHScalarDensity a (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) p)) ∧
    HasDerivAt (sameEHRelativeFieldAction a (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) d) 0 0 :=
  ⟨fun s => same_eh_relative_field_action_integrable a _ (compact_curved_field_smooth a _ f h) d s,
    compact_curved_field_stationary_for_all_compact_variations a f h d⟩

end AASCKleinGordon.CurvedKG
