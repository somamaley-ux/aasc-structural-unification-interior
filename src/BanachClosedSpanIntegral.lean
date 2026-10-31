import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open MeasureTheory Filter Topology
namespace AASCKleinGordon

/-- A genuine Bochner integral stays in a closed complex submodule.
No density statement or Schwartz-valued integral is assumed. -/
theorem wick_integral_mem_closed_submodule {X B : Type*} [MeasurableSpace X]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (μ : Measure X) (V : Submodule ℂ B) (hV : IsClosed (V : Set B))
    (F : X → B) (hF : Integrable F μ) (hmem : ∀ᵐ x ∂μ,F x∈V) :
    (∫ x,F x ∂μ)∈V := by
  letI : IsClosed (V : Set B) := hV
  let Q : B →L[ℂ] B ⧸ V := V.mkQ.mkContinuous 1 (fun b => by
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le V b)
  have hzero : (fun x => Q (F x))=ᵐ[μ] (fun _ => 0) := by
    filter_upwards [hmem] with x hx
    exact (Submodule.Quotient.mk_eq_zero V).mpr hx
  have hi : Q (∫ x,F x ∂μ)=0 := by
    rw [← Q.integral_comp_comm hF,integral_congr_ae hzero,integral_zero]
  exact (Submodule.Quotient.mk_eq_zero V).mp hi

end AASCKleinGordon
