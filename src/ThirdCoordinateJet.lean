import C2MetricNormalChart

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def scalarThirdPartial (f : CoordinatePoint → ℝ) (p : CoordinatePoint) (a b c : Fin 4) : ℝ :=
  scalarSecondPartial (fun x => scalarPartial f x a) p b c

theorem c3_scalarPartial_c2 (f : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 3 f p) (a : Fin 4) :
    ContDiffAt ℝ 2 (fun x => scalarPartial f x a) p := by
  exact (regular.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const

theorem scalarThirdPartial_swap_last (f : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 3 f p) (a b c : Fin 4) :
    scalarThirdPartial f p a b c = scalarThirdPartial f p a c b :=
  c2_scalarSecondPartial_symmetric _ p (c3_scalarPartial_c2 f p regular a) b c

theorem scalarThirdPartial_swap_first (f : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 3 f p) (a b c : Fin 4) :
    scalarThirdPartial f p a b c = scalarThirdPartial f p b a c := by
  have hs : ∀ᶠ x in nhds p,
      scalarSecondPartial f x a b = scalarSecondPartial f x b a := by
    have h := (regular.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).eventually (by norm_num)
    filter_upwards [h] with x hx
    exact c2_scalarSecondPartial_symmetric f x hx a b
  have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hs
  exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single c 1)) hd

def coordinateThirdJet (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint) : Tensor4 :=
  fun i a c d => scalarSecondPartial (fun x => coordinateJacobian F x i a) p c d

theorem coordinateThirdJet_cubic_laws (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F p) : CubicCoordinateLaws (coordinateThirdJet F p) := by
  have hi (i : Fin 4) : ContDiffAt ℝ 3 (fun x => F x i) p :=
    (coordinateProjection i).contDiff.contDiffAt.comp p regular
  constructor
  · intro i a c d
    exact scalarThirdPartial_swap_first (fun x => F x i) p (hi i) a c d
  · intro i a c d
    exact scalarThirdPartial_swap_last (fun x => F x i) p (hi i) a c d

theorem c3_coordinateJacobian_c2 (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F p) (i a : Fin 4) :
    ContDiffAt ℝ 2 (fun x => coordinateJacobian F x i a) p := by
  have hi : ContDiffAt ℝ 3 (fun x => F x i) p :=
    (coordinateProjection i).contDiff.contDiffAt.comp p regular
  exact c3_scalarPartial_c2 _ p hi a

#print axioms c3_scalarPartial_c2
#print axioms scalarThirdPartial_swap_last
#print axioms scalarThirdPartial_swap_first
#print axioms coordinateThirdJet_cubic_laws
#print axioms c3_coordinateJacobian_c2
end
end AASCSemanticExhaustion
