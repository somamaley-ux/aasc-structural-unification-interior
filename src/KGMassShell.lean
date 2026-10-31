import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Current Module B sections13 and24.1. These are explicit downstream
free-scalar formulas with declared positive mass and light-speed anchors.
No AASC role, Hilbert representation or operator attachment is inferred
from defining a mass shell. -/
noncomputable section
namespace AASCKleinGordon

structure Parameters where
  mass : ℝ
  speed : ℝ
  hbar : ℝ
  mass_pos : 0 < mass
  speed_pos : 0 < speed
  hbar_pos : 0 < hbar

abbrev Momentum := Fin 3 → ℝ
abbrev FourMomentum := Fin 4 → ℝ

def momentumSq (p : Momentum) : ℝ := p 0^2+p 1^2+p 2^2

theorem momentumSq_nonneg (p : Momentum) : 0 ≤ momentumSq p := by
  unfold momentumSq
  positivity

def energy (a : Parameters) (p : Momentum) : ℝ :=
  Real.sqrt (a.mass^2*a.speed^4+a.speed^2*momentumSq p)

theorem energy_radicand_pos (a : Parameters) (p : Momentum) :
    0 < a.mass^2*a.speed^4+a.speed^2*momentumSq p := by
  have hm := a.mass_pos
  have hc := a.speed_pos
  have hp := momentumSq_nonneg p
  positivity

theorem energy_pos (a : Parameters) (p : Momentum) : 0 < energy a p :=
  Real.sqrt_pos.2 (energy_radicand_pos a p)

theorem energy_sq (a : Parameters) (p : Momentum) :
    energy a p^2=a.mass^2*a.speed^4+a.speed^2*momentumSq p :=
  Real.sq_sqrt (le_of_lt (energy_radicand_pos a p))

def massShell (a : Parameters) (p : Momentum) : FourMomentum :=
  ![energy a p/a.speed,p 0,p 1,p 2]

def minkowskiDot (p q : FourMomentum) : ℝ :=
  -(p 0*q 0)+p 1*q 1+p 2*q 2+p 3*q 3

theorem minkowskiDot_comm (p q : FourMomentum) : minkowskiDot p q=minkowskiDot q p := by
  unfold minkowskiDot
  ring

theorem massShell_on_shell (a : Parameters) (p : Momentum) :
    minkowskiDot (massShell a p) (massShell a p)= -(a.mass^2*a.speed^2) := by
  have hc : a.speed≠0 := ne_of_gt a.speed_pos
  have he := energy_sq a p
  change -(energy a p/a.speed*(energy a p/a.speed)) + p 0*p 0+p 1*p 1+p 2*p 2 = _
  field_simp
  dsimp [momentumSq] at he
  nlinarith [he]

def metricSign (μ : Fin 4) : ℝ := if μ=0 then -1 else 1
def minkowskiMetric (μ ν : Fin 4) : ℝ := if μ=ν then metricSign μ else 0

def scalarMatrixElement (a : Parameters) (p' p : FourMomentum) (μ ν : Fin 4) : ℝ :=
  p' μ*p ν+p' ν*p μ-minkowskiMetric μ ν*(minkowskiDot p' p+a.mass^2*a.speed^2)

theorem scalarMatrixElement_symmetric (a : Parameters) (p' p : FourMomentum) (μ ν : Fin 4) :
    scalarMatrixElement a p' p μ ν=scalarMatrixElement a p' p ν μ := by
  have h : minkowskiMetric μ ν=minkowskiMetric ν μ := by
    by_cases e : μ=ν
    · subst ν; rfl
    · simp [minkowskiMetric,e,Ne.symm e]
  simp only [scalarMatrixElement,h]
  ring

theorem forward_matrix_element (a : Parameters) (p : Momentum) (μ ν : Fin 4) :
    scalarMatrixElement a (massShell a p) (massShell a p) μ ν=
      2*massShell a p μ*massShell a p ν := by
  rw [scalarMatrixElement,massShell_on_shell]
  ring

theorem rest_energy (a : Parameters) : energy a 0=a.mass*a.speed^2 := by
  have he : a.mass^2*a.speed^4+a.speed^2*momentumSq (0 : Momentum) =
      (a.mass*a.speed^2)^2 := by simp [momentumSq]; ring
  rw [energy,he,Real.sqrt_sq]
  exact mul_nonneg (le_of_lt a.mass_pos) (sq_nonneg _)

theorem free_scalar_forward_source_nonzero (a : Parameters) :
    scalarMatrixElement a (massShell a 0) (massShell a 0) 0 0 > 0 := by
  rw [forward_matrix_element]
  change 0 < 2*(energy a 0/a.speed)*(energy a 0/a.speed)
  have hr : 0 < energy a 0/a.speed := div_pos (energy_pos a 0) a.speed_pos
  nlinarith [sq_pos_of_pos hr]

end AASCKleinGordon
