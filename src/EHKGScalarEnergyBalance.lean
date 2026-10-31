import EHKGScalarEnergyJets
import EHKGCompactCausalTube

/-! The finite-window energy hypotheses are discharged for actual scalar
jets. The local equation is required only on the named compact tube. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem jet_position_joint_smooth (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (jetPosition F)) := regular.comp coordinateSpatialSplit.symm.contDiff

theorem jet_velocity_joint_smooth (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (jetVelocity F)) :=
  (scalar_partial_smooth F regular 0).comp coordinateSpatialSplit.symm.contDiff

theorem jet_gradient_joint_smooth (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (jetGradient F)) :=
  momentumEuclidean.contDiff.comp (contDiff_pi.mpr (fun i =>
    (scalar_partial_smooth F regular i.succ).comp coordinateSpatialSplit.symm.contDiff))

theorem jet_velocity_spatial_regular (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    Differentiable ℝ (jetVelocity F t) :=
  ((jet_velocity_joint_smooth F regular).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)

theorem jet_gradient_spatial_regular (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (i : Fin 3) : Differentiable ℝ (fun x => jetGradient F t x i) :=
  ((scalar_partial_smooth F regular i.succ).comp
    (coordinateSpatialSplit.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))).differentiable (by simp)

def jetFluxComponent (F : CoordinatePoint → ℝ) (i : Fin 3) (p : CoordinatePoint) : ℝ :=
  scalarPartial F p 0 * scalarPartial F p i.succ

theorem jet_flux_component_smooth (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (jetFluxComponent F i) :=
  (scalar_partial_smooth F regular 0).mul (scalar_partial_smooth F regular i.succ)

theorem jet_flux_spatial_derivative (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    fderiv ℝ (fun y => flatEnergyFlux (jetVelocity F) (jetGradient F) t y i) x (kgSpatialDirection i) =
      scalarPartial (jetFluxComponent F i) (spaceTimePoint t x) i.succ :=
  scalar_join_spatial_partial _ (jet_flux_component_smooth F regular i) t x i

theorem jet_flux_spatial_regular (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (i : Fin 3) :
    Differentiable ℝ (fun x => flatEnergyFlux (jetVelocity F) (jetGradient F) t x i) :=
  ((jet_flux_component_smooth F regular i).comp
    (coordinateSpatialSplit.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))).differentiable (by simp)

theorem jet_flux_spatial_derivative_joint_continuous (F : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin 3) :
    Continuous (fun z : ℝ × KGSpatialSpace =>
      fderiv ℝ (fun y => flatEnergyFlux (jetVelocity F) (jetGradient F) z.1 y i) z.2 (kgSpatialDirection i)) := by
  simp_rw [jet_flux_spatial_derivative F regular]
  exact ((scalar_partial_smooth _ (jet_flux_component_smooth F regular i) i.succ).comp
    coordinateSpatialSplit.symm.contDiff).continuous

theorem jet_flux_divergence_joint_continuous (F : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (fun z : ℝ × KGSpatialSpace =>
      kgSpatialDivergence (flatEnergyFlux (jetVelocity F) (jetGradient F) z.1) z.2) := by
  apply continuous_finset_sum
  intro i hi
  exact jet_flux_spatial_derivative_joint_continuous F regular i

theorem flat_residual_smooth (mu2 : ℝ) (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (flatScalarResidual mu2 F) := by
  exact ((((scalar_second_partial_smooth F regular 0 0).sub (scalar_second_partial_smooth F regular 1 1)).sub
    (scalar_second_partial_smooth F regular 2 2)).sub (scalar_second_partial_smooth F regular 3 3)).add
      (contDiff_const.mul regular)

def jetEnergyDerivative (mu : ℝ) (F : CoordinatePoint → ℝ) (t : ℝ) (x : KGSpatialSpace) : ℝ :=
  kgSpatialDivergence (flatEnergyFlux (jetVelocity F) (jetGradient F) t) x +
    jetVelocity F t x * flatScalarResidual (mu ^ 2) F (spaceTimePoint t x)

theorem jet_energy_derivative_joint_continuous (mu : ℝ) (F : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) : Continuous (Function.uncurry (jetEnergyDerivative mu F)) :=
  (jet_flux_divergence_joint_continuous F regular).add
    ((jet_velocity_joint_smooth F regular).continuous.mul
      (((flat_residual_smooth (mu ^ 2) F regular).comp coordinateSpatialSplit.symm.contDiff).continuous))

theorem jet_actual_energy_derivative (mu : ℝ) (F : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => flatEnergyDensity mu (jetPosition F) (jetVelocity F) (jetGradient F) s x)
      (jetEnergyDerivative mu F t x) t := by
  have actual := ((((jet_velocity_time F regular t x).pow 2).add (jet_gradient_time F regular t x).norm_sq).add
    (((jet_position_time F regular t x).pow 2).const_mul (mu ^ 2))).div_const 2
  convert actual using 1
  rw [jetEnergyDerivative]
  change kgSpatialDivergence (fun y => flatKGFlux (jetVelocity F t y) (jetGradient F t y)) x +
    jetVelocity F t x * flatScalarResidual (mu ^ 2) F (spaceTimePoint t x) = _
  rw [flatKGFlux_divergence (jetVelocity F t) (jetGradient F t)
      (jet_velocity_spatial_regular F regular t) (jet_gradient_spatial_regular F regular t) x
      (jetVelocityGradient F t x) (jet_velocity_spatial_partial F regular t x),
      jet_gradient_divergence F regular]
  simp only [flatScalarResidual, jetPosition, jetVelocity, pow_one, Nat.cast_ofNat]
  ring

theorem smooth_scalar_window_vanishes (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (mu R T : ℝ) (center : KGSpatialSpace) (mass : mu ≠ 0) (time : 0 ≤ T) (radius : T < R)
    (equation : ∀ p ∈ compactCausalTube R T center, flatScalarResidual (mu ^ 2) F p = 0)
    (initial : ∀ x ∈ Metric.closedBall center R,
      F (spaceTimePoint 0 x) = 0 ∧ scalarPartial F (spaceTimePoint 0 x) 0 = 0 ∧
        ∀ i : Fin 3, scalarPartial F (spaceTimePoint 0 x) i.succ = 0) :
    F (spaceTimePoint T center) = 0 := by
  have fluxDerivative (t : ℝ) (i : Fin 3) : Continuous (fun x : KGSpatialSpace =>
      fderiv ℝ (fun y => flatEnergyFlux (jetVelocity F) (jetGradient F) t y i) x (kgSpatialDirection i)) := by
    simp_rw [jet_flux_spatial_derivative F regular]
    have param : ContDiff ℝ (⊤ : ℕ∞) (fun x : KGSpatialSpace => (t, x)) := contDiff_const.prodMk contDiff_id
    exact ((scalar_partial_smooth _ (jet_flux_component_smooth F regular i) i.succ).comp
      (coordinateSpatialSplit.symm.contDiff.comp param)).continuous
  change jetPosition F T center = 0
  apply localized_window_vanishes R mu T center mass time radius (jetPosition F) (jetVelocity F)
    (jetGradient F) (jetEnergyDerivative mu F)
    (jet_position_joint_smooth F regular).continuous (jet_velocity_joint_smooth F regular).continuous
    (jet_gradient_joint_smooth F regular).continuous (jet_energy_derivative_joint_continuous mu F regular)
    (jet_actual_energy_derivative mu F regular) (jet_flux_divergence_joint_continuous F regular)
    (jet_flux_spatial_regular F regular)
    fluxDerivative
  · intro t ht x hx
    have inTube : spaceTimePoint t x ∈ compactCausalTube R T center := by
      refine ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    simp only [jetEnergyDerivative, equation _ inTube, mul_zero, add_zero]
  · intro x hx
    obtain ⟨position, velocity, gradient⟩ := initial x hx
    refine ⟨position, velocity, ?_⟩
    ext i
    exact gradient i

end AASCKleinGordon.CurvedKG
