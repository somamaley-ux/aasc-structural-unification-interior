import EHKGCompactCausalTube
import C2LocalSecondJetCalculus

/-! Exact local time-reflection rules, using the retained actual C2 chain
rule. These will supply the past half of local uniqueness. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def timeReflectionSign (c : Fin 4) : ℝ := if c = 0 then -1 else 1

def timeReflectionCLM : CoordinatePoint →L[ℝ] CoordinatePoint :=
  ContinuousLinearMap.pi (fun c => timeReflectionSign c •
    (ContinuousLinearMap.proj c : CoordinatePoint →L[ℝ] ℝ))

theorem time_reflection_coordinate (p : CoordinatePoint) (c : Fin 4) :
    timeReflectionCLM p c = timeReflectionSign c * p c := rfl

theorem time_reflection_time (p : CoordinatePoint) : timeReflectionCLM p 0 = -p 0 := by
  simp [time_reflection_coordinate, timeReflectionSign]

theorem time_reflection_spatial (p : CoordinatePoint) :
    coordinateSpatialCLM (timeReflectionCLM p) = coordinateSpatialCLM p := by
  ext i
  change timeReflectionSign i.succ * p i.succ = p i.succ
  simp [timeReflectionSign]

theorem time_reflection_involutive (p : CoordinatePoint) : timeReflectionCLM (timeReflectionCLM p) = p := by
  funext c
  rw [time_reflection_coordinate, time_reflection_coordinate]
  by_cases zero : c = 0 <;> simp [timeReflectionSign, zero]

theorem time_reflection_unit (c : Fin 4) :
    timeReflectionCLM (Pi.single c (1 : ℝ) : CoordinatePoint) =
      timeReflectionSign c • (Pi.single c (1 : ℝ) : CoordinatePoint) := by
  funext i
  change timeReflectionSign i * (Pi.single c (1 : ℝ) : CoordinatePoint) i =
    timeReflectionSign c * (Pi.single c (1 : ℝ) : CoordinatePoint) i
  by_cases equal : i = c
  · subst i; rfl
  · simp [Pi.single_apply, equal, Ne.symm equal]

theorem time_reflection_gauge (p : CoordinatePoint) : diamondGauge (timeReflectionCLM p) = diamondGauge p := by
  change |timeReflectionCLM p 0| + ‖coordinateSpatialCLM (timeReflectionCLM p)‖ =
    |p 0| + ‖coordinateSpatialCLM p‖
  rw [time_reflection_time, time_reflection_spatial, abs_neg]

theorem time_reflection_diamond (nu : ℝ) (p : CoordinatePoint) :
    timeReflectionCLM p ∈ protectedDiamond nu ↔ p ∈ protectedDiamond nu := by
  change diamondGauge (timeReflectionCLM p) < protectedRadius nu ↔ _
  rw [time_reflection_gauge]
  rfl

theorem time_reflection_central (x : KGSpatialSpace) : timeReflectionCLM (centralLeafPoint x) = centralLeafPoint x := by
  apply coordinateSpatialSplit.injective
  apply Prod.ext
  · change timeReflectionCLM (centralLeafPoint x) 0 = centralLeafPoint x 0
    rw [time_reflection_time, central_leaf_time, neg_zero]
  · exact time_reflection_spatial (centralLeafPoint x)

theorem scalar_second_diagonal_time_reflection (F : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 2 F (timeReflectionCLM p)) (c : Fin 4) :
    scalarSecondPartial (fun x => F (timeReflectionCLM x)) p c c =
      scalarSecondPartial F (timeReflectionCLM p) c c := by
  rw [c2_local_linear_composition_second F timeReflectionCLM p regular,
    c2_scalarSecondPartial_full_second_derivative F _ regular, time_reflection_unit]
  fin_cases c <;> simp [timeReflectionSign]

theorem flat_residual_time_reflection (mu2 : ℝ) (F : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 2 F (timeReflectionCLM p)) :
    flatScalarResidual mu2 (fun x => F (timeReflectionCLM x)) p = flatScalarResidual mu2 F (timeReflectionCLM p) := by
  simp only [flatScalarResidual, scalar_second_diagonal_time_reflection F p regular]

theorem scalar_time_partial_time_reflection (F : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : DifferentiableAt ℝ F (timeReflectionCLM p)) :
    scalarPartial (fun x => F (timeReflectionCLM x)) p 0 = -scalarPartial F (timeReflectionCLM p) 0 := by
  have chain := regular.hasFDerivAt.comp p timeReflectionCLM.hasFDerivAt
  have derivative := chain.fderiv
  change fderiv ℝ (fun x => F (timeReflectionCLM x)) p = _ at derivative
  change fderiv ℝ (fun x => F (timeReflectionCLM x)) p (Pi.single 0 1) = _
  rw [derivative]
  change fderiv ℝ F (timeReflectionCLM p) (timeReflectionCLM (Pi.single 0 (1 : ℝ) : CoordinatePoint)) = _
  rw [time_reflection_unit]
  simp [timeReflectionSign, scalarPartial]

end AASCKleinGordon.CurvedKG
