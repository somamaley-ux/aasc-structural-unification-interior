import SKGConformalMetricCalculus

/-! Finite algebra used only after actual derivatives are identified. The
Hessian symmetry required here is supplied by the actual C2 field later. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open AASCSemanticExhaustion
open scoped BigOperators
namespace AASCKleinGordon.SameActionSource

def scalarStressJetValue (l phi mu2 : ℝ) (P : Fin 4 → ℝ) (a b : Fin 4) : ℝ :=
  P a * P b - (1 / 2 : ℝ) * metric a b * (scalarFlatKinetic P + mu2 * l * phi ^ 2)

def scalarStressJetPartial (l phi mu2 : ℝ) (P W : Fin 4 → ℝ)
    (H : Fin 4 → Fin 4 → ℝ) (c a b : Fin 4) : ℝ :=
  H a c * P b + P a * H b c - metric a b *
    ((∑ i : Fin 4, metric i i * P i * H i c) +
      mu2 * ((1 / 2 : ℝ) * W c * phi ^ 2 + l * phi * P c))

def scalarConformalConnectionJet (l : ℝ) (W : Fin 4 → ℝ) (e b c : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * l⁻¹ *
    ((if e = b then W c else 0) + (if e = c then W b else 0) - metric b c * metric e e * W e)

def scalarStressJetDivergence (l phi mu2 : ℝ) (P W : Fin 4 → ℝ)
    (H : Fin 4 → Fin 4 → ℝ) (b : Fin 4) : ℝ :=
  l⁻¹ * ∑ a : Fin 4, metric a a *
    (scalarStressJetPartial l phi mu2 P W H a a b -
      (∑ e : Fin 4, scalarConformalConnectionJet l W e a a * scalarStressJetValue l phi mu2 P e b) -
      (∑ e : Fin 4, scalarConformalConnectionJet l W e a b * scalarStressJetValue l phi mu2 P a e))

theorem scalar_stress_off_shell_jet_algebra (l phi mu2 : ℝ) (P W : Fin 4 → ℝ)
    (H : Fin 4 → Fin 4 → ℝ) (nonzero : l ≠ 0)
    (symmetric : ∀ a b, H a b = H b a) (b : Fin 4) :
    scalarStressJetDivergence l phi mu2 P W H b =
      (l⁻¹ * (∑ i : Fin 4, metric i i * H i i) +
        l⁻¹ ^ 2 * (∑ i : Fin 4, metric i i * W i * P i) - mu2 * phi) * P b := by
  have h01 := symmetric 0 1
  have h02 := symmetric 0 2
  have h03 := symmetric 0 3
  have h12 := symmetric 1 2
  have h13 := symmetric 1 3
  have h23 := symmetric 2 3
  fin_cases b <;>
    simp [scalarStressJetDivergence, scalarStressJetPartial, scalarStressJetValue,
      scalarConformalConnectionJet, scalarFlatKinetic, metric, Matrix.diagonal_apply,
      Fin.sum_univ_succ]
  all_goals simp only [h01, h02, h03, h12, h13, h23]
  all_goals field_simp [nonzero]
  all_goals ring

end AASCKleinGordon.SameActionSource
