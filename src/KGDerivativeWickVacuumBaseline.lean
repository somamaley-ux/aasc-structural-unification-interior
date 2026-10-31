import KGDerivativeWickStateLaws
import KGDerivativeWickCutoffIndependence

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem originalDerivativeWickBilocalCore_vacuum (a : Parameters) (s : ℝ)
    (d0 d1 x y : Spacetime) :
    originalDerivativeWickBilocalCore a s vacuumCore vacuumCore d0 d1 x y = 0 := by
  rw [← originalWickBilocalCore_mixed_fderiv]
  simp_rw [originalWickBilocalCore_vacuum]
  simp

theorem originalDerivativeWickMatrix_vacuum (a : Parameters) (s : ℝ)
    (d0 d1 x : Spacetime) :
    originalDerivativeWickMatrix a s vacuumCore vacuumCore d0 d1 x = 0 :=
  originalDerivativeWickBilocalCore_vacuum a s d0 d1 x x

theorem originalDerivativeWickDistribution_vacuum (a : Parameters) (s : ℝ)
    (d0 d1 : Spacetime) :
    originalDerivativeWickDistribution a s vacuumCore vacuumCore d0 d1 = 0 := by
  ext h
  simp [originalDerivativeWickDistribution_pairing, originalDerivativeWickMatrix_vacuum]

theorem originalDerivativeWickDistribution_any_cutoff_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (N : ℕ)
    (hu : WickCoreTailBound u N) (hv : WickCoreTailBound v N)
    (d0 d1 : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    originalDerivativeWickDistribution a s u v d0 d1 h =
      ∫ x,h x * originalDerivativeWickBilocalCoreAt a s u v N d0 d1 x x := by
  rw [originalDerivativeWickDistribution_pairing]
  simp_rw [originalDerivativeWickMatrix_eq_any_cutoff a s u v N hu hv]

theorem originalDerivativeWickDistributionSesqForm_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    originalDerivativeWickDistributionSesqForm a s d0 d1 u v h =
      ∫ x,h x * originalDerivativeWickMatrix a s u v d0 d1 x :=
  originalDerivativeWickDistribution_pairing a s u v d0 d1 h

end AASCKleinGordon
