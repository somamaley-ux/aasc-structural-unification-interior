import KGOriginalWickBilocalHermiticity
import KGOriginalWickFlatWard

/-! Hermiticity of the SAME action-identified weak tensor on arbitrary
original finite-core state pairs. This is not an operator-domain theorem. -/
noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap ComplexConjugate
namespace AASCKleinGordon
open SchwartzOperations

theorem wick_real_fderiv_conjugate (F G : Spacetime → ℂ)
    (h : ∀ y,star (F y)=G y) (x d : Spacetime) :
    star (fderiv ℝ F x d)=fderiv ℝ G x d := by
  have heq : (fun y => star (F y))=G := funext h
  have hd := congrArg (fun f : Spacetime → ℂ => fderiv ℝ f x d) heq
  dsimp only at hd
  rw [fderiv_star] at hd
  exact hd

theorem originalFirstDerivativeWickBilocalCore_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 x y : Spacetime) :
    star (originalFirstDerivativeWickBilocalCore a s u v d0 x y)=
      originalFirstDerivativeWickBilocalCore a s v u d0 x y := by
  simpa only [originalWickBilocalCore_fderiv_left] using
    wick_real_fderiv_conjugate (fun z => originalWickBilocalCore a s u v z y)
      (fun z => originalWickBilocalCore a s v u z y)
      (fun z => originalWickBilocalCore_hermitian a s u v z y) x d0

theorem originalDerivativeWickBilocalCore_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 x y : Spacetime) :
    star (originalDerivativeWickBilocalCore a s u v d0 d1 x y)=
      originalDerivativeWickBilocalCore a s v u d0 d1 x y := by
  have hd := wick_real_fderiv_conjugate
    (fun z => originalFirstDerivativeWickBilocalCore a s u v d0 x z)
    (fun z => originalFirstDerivativeWickBilocalCore a s v u d0 x z)
    (fun z => originalFirstDerivativeWickBilocalCore_hermitian a s u v d0 x z) y d1
  have hm (w z : FiniteParticleCore) :
      fderiv ℝ (fun r => originalFirstDerivativeWickBilocalCore a s w z d0 x r) y d1=
        originalDerivativeWickBilocalCore a s w z d0 d1 x y := by
    simpa only [originalWickBilocalCore_fderiv_left] using
      originalWickBilocalCore_mixed_fderiv a s w z x y d0 d1
  simpa only [hm] using hd

theorem originalWickSquareMatrix_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x : Spacetime) :
    star (originalWickSquareMatrix a s u v x)=originalWickSquareMatrix a s v u x :=
  originalWickBilocalCore_hermitian a s u v x x

theorem originalDerivativeWickMatrix_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 x : Spacetime) :
    star (originalDerivativeWickMatrix a s u v d0 d1 x)=
      originalDerivativeWickMatrix a s v u d0 d1 x :=
  originalDerivativeWickBilocalCore_hermitian a s u v d0 d1 x x

theorem originalWickScalarLagrangianMatrix_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x : Spacetime) :
    star (originalWickScalarLagrangianMatrix a s u v x)=originalWickScalarLagrangianMatrix a s v u x := by
  simp only [originalWickScalarLagrangianMatrix,star_add,star_neg,star_mul,
    originalDerivativeWickMatrix_hermitian,originalWickSquareMatrix_hermitian]
  simp <;> ring

theorem original_wick_scalar_stress_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (x : Spacetime) :
    star (originalWickScalarStressCandidateMatrix a s u v i j x)=
      originalWickScalarStressCandidateMatrix a s v u i j x := by
  simp only [originalWickScalarStressCandidateMatrix,star_sub,star_add,star_mul,
    originalDerivativeWickMatrix_hermitian,originalWickScalarLagrangianMatrix_hermitian]
  simp <;> ring

theorem original_wick_raised_stress_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (x : Spacetime) :
    star (originalWickScalarStressRaisedMatrix a s u v i j x)=
      originalWickScalarStressRaisedMatrix a s v u i j x := by
  simp [originalWickScalarStressRaisedMatrix,original_wick_scalar_stress_hermitian]

theorem original_wick_scalar_stress_diagonal_real (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (i j : Fin 4) (x : Spacetime) :
    (originalWickScalarStressRaisedMatrix a s u u i j x).im=0 := by
  have h := congrArg Complex.im (original_wick_raised_stress_hermitian a s u u i j x)
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

theorem original_wick_stress_distribution_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    star (originalWickRaisedStressDistribution a s u v i j h)=
      originalWickRaisedStressDistribution a s v u i j (conjugateSchwartzCLM h) := by
  rw [original_wick_raised_stress_distribution_pairing,original_wick_raised_stress_distribution_pairing]
  change conj (∫ x,h x*originalWickScalarStressRaisedMatrix a s u v i j x)=_
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [map_mul,conjugateSchwartzCLM_apply]
    rw [show conj (originalWickScalarStressRaisedMatrix a s u v i j x)=
      originalWickScalarStressRaisedMatrix a s v u i j x from
        original_wick_raised_stress_hermitian a s u v i j x]
    rfl)

end AASCKleinGordon
