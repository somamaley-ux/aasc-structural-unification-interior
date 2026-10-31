import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

theorem lp_comp_inverse (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (hi : MeasurePreserving e.symm ν μ) (f : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving e.symm hi (Lp.compMeasurePreserving e he f)=f := by
  apply Lp.ext
  have h₁ := Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving e he f) hi
  have h₂ := hi.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f he)
  filter_upwards [h₁,h₂] with x hx hy
  simpa only [Function.comp_apply,e.apply_symm_apply] using hx.trans hy

def lpMeasureEquivalence (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (hi : MeasurePreserving e.symm ν μ) : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := Lp.compMeasurePreserving e he
  invFun := Lp.compMeasurePreserving e.symm hi
  left_inv := lp_comp_inverse e he hi
  right_inv := lp_comp_inverse e.symm hi he
  map_add' := (Lp.compMeasurePreserving e he).map_add
  map_smul' := (Lp.compMeasurePreservingₗ ℂ e he).map_smul
  norm_map' := fun f => Lp.norm_compMeasurePreserving f he

end AASCKleinGordon
