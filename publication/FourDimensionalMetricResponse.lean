import SmoothMetricResponse
import FourDimensionalDiv2

/-! Interface between the dimension-four Lovelock obstruction and the geometric
response on the original metric germs. The coefficient input records the
symmetries of the actual second derivative; it does not postulate its vanishing.
Deriving those differential symmetries from geometric naturality and off-shell
closure for arbitrary smooth natural tensors is the external Lovelock step. -/
namespace AASCSemanticExhaustion
noncomputable section
open scoped Matrix.Norms.Elementwise

private abbrev HessianSlots := (Fin 4 × Fin 4) × (Fin 4 × Fin 4)

/-- Coefficient contraction for two full symmetric Hessian perturbations.
The two leading metric factors lower the output indices at the normalized
Lorentz metric. Both ordered pairs of indices for each perturbation are summed. -/
def normalResponseSecondContraction (T : Div2Four.Pairs → ℝ)
    (U V : metricHessianSpace) (i j : Fin 4) : ℝ :=
  metric i i * metric j j *
    ∑ a : HessianSlots, ∑ b : HessianSlots,
      U.val a.1.1 a.1.2 a.2.1 a.2.2 *
      V.val b.1.1 b.1.2 b.2.1 b.2.2 *
      T (Div2Four.pairs [(i, j), a.1, a.2, b.1, b.2])

/-- At every normalized polynomial metric probe, the actual second derivative
has components carrying the five-pair exchange and cyclic symmetries.
This differential input is distinct from smoothness of the response map. -/
def NormalResponseSecondSymmetries (E : MetricFieldResponse) : Prop :=
  ∀ H : metricHessianSpace, ∃ T : Div2Four.Pairs → ℝ, Div2Four.Cyclic T ∧
    ∀ U V : metricHessianSpace, ∀ i j : Fin 4,
      (fderiv ℝ (fderiv ℝ (metricHessianResponseAt E 0)) H U V) i j =
        normalResponseSecondContraction T U V i j

theorem response_hessian_zero_of_four_dimensional_symmetries
    (E : MetricFieldResponse) (hs : NormalResponseSecondSymmetries E)
    (H : metricHessianSpace) : fderiv ℝ (fderiv ℝ (metricHessianResponseAt E 0)) H = 0 := by
  obtain ⟨T, hT, hc⟩ := hs H
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  ext i j
  change (fderiv ℝ (fderiv ℝ (metricHessianResponseAt E 0)) H U V) i j = 0
  rw [hc]
  have hz (a b : HessianSlots) : T (Div2Four.pairs [(i,j),a.1,a.2,b.1,b.2]) = 0 :=
    Div2Four.component_zero T hT _ rfl
  simp [normalResponseSecondContraction, hz]

/-- On the four-dimensional branch the differential symmetry certificate
forces the affine law on actual curvature, through the dimension bound. -/
theorem original_curvature_affine_of_four_dimensional_symmetries
    (E : MetricFieldResponse) (hn : RegularLorentzResponseNatural E)
    (hl : RegularLorentzTwoJetLocal E)
    (hF : Differentiable ℝ (metricHessianResponseAt E 0))
    (hD : Differentiable ℝ (fderiv ℝ (metricHessianResponseAt E 0)))
    (hs : NormalResponseSecondSymmetries E) :
    OriginalCurvatureFirstResponse E :=
  original_curvature_affine_of_vanishing_response_hessian E hn hl hF hD
    (response_hessian_zero_of_four_dimensional_symmetries E hs)

/-- The geometric classification takes differentiated symmetries instead of
affine response. Its conclusion holds on the paper's original regular envelope. -/
theorem unique_einstein_of_four_dimensional_symmetries
    (E : MetricFieldResponse) (hn : RegularLorentzResponseNatural E)
    (hl : RegularLorentzTwoJetLocal E)
    (hF : Differentiable ℝ (metricHessianResponseAt E 0))
    (hD : Differentiable ℝ (fderiv ℝ (metricHessianResponseAt E 0)))
    (hs : NormalResponseSecondSymmetries E)
    (symmetric : ∀ g p, C2LorentzMetricAt g p → ∀ i j, E g p i j = E g p j i)
    (closed : GeneralNormalMetricResponseClosure E) (active : FullLorentzEnvelopeResponseActive E) :
    ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ CoordinateEinsteinResponseForm E ac.1 ac.2 :=
  original_curvature_general_response_has_unique_einstein_form E hn hl
    (original_curvature_affine_of_four_dimensional_symmetries E hn hl hF hD hs)
    symmetric closed active

/-- A single finite-dimensional regularity condition suffices for the checked
analytic step. It is imposed on the response as the metric Hessian varies. -/
theorem c2_profile_unique_einstein_of_four_dimensional_symmetries
    (E : MetricFieldResponse) (hn : RegularLorentzResponseNatural E)
    (hl : RegularLorentzTwoJetLocal E)
    (regular : ContDiff ℝ 2 (metricHessianResponseAt E 0))
    (hs : NormalResponseSecondSymmetries E)
    (symmetric : ∀ g p, C2LorentzMetricAt g p → ∀ i j, E g p i j = E g p j i)
    (closed : GeneralNormalMetricResponseClosure E) (active : FullLorentzEnvelopeResponseActive E) :
    ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ CoordinateEinsteinResponseForm E ac.1 ac.2 :=
  unique_einstein_of_four_dimensional_symmetries E hn hl
    (regular.differentiable (by norm_num))
    ((regular.fderiv_right (m := 1) (by norm_num)).differentiable (by simp))
    hs symmetric closed active

end
end AASCSemanticExhaustion
