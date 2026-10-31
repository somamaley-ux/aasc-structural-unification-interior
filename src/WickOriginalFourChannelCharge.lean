import WickPhysicalPureChargeZero
import WickPhysicalTwoMixedCharges

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
namespace AASCKleinGordon

theorem wick_original_all_channel_hypersurface_integrable (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (τ : ℝ) :
    Integrable (fun x : WickSpaceSlice =>
      wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x))) := by
  fin_cases k
  · exact wick_original_pure_hypersurface_integrable a n u v 0 j (Or.inl rfl) τ
  · exact wick_original_mixed_hypersurface_integrable a n u v 1 j (Or.inl rfl) τ
  · exact wick_original_mixed_hypersurface_integrable a n u v 2 j (Or.inr rfl) τ
  · exact wick_original_pure_hypersurface_integrable a n u v 3 j (Or.inr rfl) τ

theorem wick_original_raised_stress_hypersurface_integrable (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    Integrable (fun x : WickSpaceSlice =>
      originalWickScalarStressRaisedMatrix a s u v 0 j (spacetimeSpatialJoin (τ,x))) := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  have hi := (integrable_finset_sum S (fun k _ =>
    (wick_original_all_channel_hypersurface_integrable a k.1 u v k.2 j τ).const_mul
      (wickCoreChannelCoefficient k.1 k.2))).const_mul ((s : ℂ)^2)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun x =>
    (original_wick_raised_stress_channel_expansion a s u v 0 j (spacetimeSpatialJoin (τ,x))).symm)

def wickOriginalHypersurfaceCharge (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (j : Fin 4) (τ : ℝ) : ℂ :=
  (a.speed : ℂ)⁻¹*∫ x : WickSpaceSlice,
    originalWickScalarStressRaisedMatrix a s u v 0 j (spacetimeSpatialJoin (τ,x))

theorem wick_original_four_channel_sector_hypersurface_charge (a : Parameters) (s : ℝ)
    (n : ℕ) (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    (s : ℂ)^2*(a.speed : ℂ)⁻¹*
      ∑ k : Fin 4,wickCoreChannelCoefficient n k*
        ∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x)) =
      wickSameTensorChargeCoefficient a s*((n+1 : ℝ) : ℂ)*
        ∫ p : Momentum,∫ r,(wignerWeight a p : ℂ)*(massShell a p j : ℂ)*
          wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  change (s : ℂ)^2*(a.speed : ℂ)⁻¹*
    (wickCoreChannelCoefficient n 0*(∫ x : WickSpaceSlice,
      wickCoreRaisedStressMatrix a n u v 0 0 j (spacetimeSpatialJoin (τ,x)))+
     (wickCoreChannelCoefficient n 1*(∫ x : WickSpaceSlice,
      wickCoreRaisedStressMatrix a n u v 1 0 j (spacetimeSpatialJoin (τ,x)))+
      (wickCoreChannelCoefficient n 2*(∫ x : WickSpaceSlice,
      wickCoreRaisedStressMatrix a n u v 2 0 j (spacetimeSpatialJoin (τ,x)))+
       (wickCoreChannelCoefficient n 3*(∫ x : WickSpaceSlice,
      wickCoreRaisedStressMatrix a n u v 3 0 j (spacetimeSpatialJoin (τ,x)))+0))))=_
  rw [wick_original_CC_hypersurface_integral_zero,wick_original_AA_hypersurface_integral_zero]
  simp only [mul_zero,zero_add,add_zero]
  exact wick_original_two_mixed_hypersurface_charges a s n u v j τ

theorem wick_original_hypersurface_charge_cutoff (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    wickOriginalHypersurfaceCharge a s u v j τ=
      wickSameTensorChargeCoefficient a s*
        ∑ n ∈ Finset.range (wickJointCoreCutoff u v),((n+1 : ℝ) : ℂ)*
          ∫ p : Momentum,∫ r,(wignerWeight a p : ℂ)*(massShell a p j : ℂ)*
            wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n := by
  unfold wickOriginalHypersurfaceCharge
  simp_rw [original_wick_raised_stress_channel_expansion]
  rw [integral_const_mul,integral_finset_sum _ (fun k _ =>
    (wick_original_all_channel_hypersurface_integrable a k.1 u v k.2 j τ).const_mul
      (wickCoreChannelCoefficient k.1 k.2))]
  have each (n : ℕ) (k : Fin 4) :
      (∫ x : WickSpaceSlice,wickCoreChannelCoefficient n k*
        wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x)))=
        wickCoreChannelCoefficient n k*(∫ x : WickSpaceSlice,
          wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x))) :=
    integral_const_mul _ _
  simp_rw [each]
  rw [Finset.product_eq_sprod]
  rw [Finset.sum_product' (Finset.range (wickJointCoreCutoff u v))
    (Finset.univ : Finset (Fin 4)) (fun n k => wickCoreChannelCoefficient n k*
    ∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x)))]
  calc
    _ = ∑ n ∈ Finset.range (wickJointCoreCutoff u v),
        (s : ℂ)^2*(a.speed : ℂ)⁻¹*
          ∑ k : Fin 4,wickCoreChannelCoefficient n k*
            ∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j
              (spacetimeSpatialJoin (τ,x)) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      simp_rw [wick_original_four_channel_sector_hypersurface_charge,mul_assoc]
      exact (Finset.mul_sum _ _ _).symm

theorem wick_original_hypersurface_charge_time_independent (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ σ : ℝ) :
    wickOriginalHypersurfaceCharge a s u v j τ=wickOriginalHypersurfaceCharge a s u v j σ := by
  rw [wick_original_hypersurface_charge_cutoff,wick_original_hypersurface_charge_cutoff]

end AASCKleinGordon
