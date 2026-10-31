import OutputGeneratorTransport
import FiniteSumTen
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
def outputCoordinateTransport (g : Fin 7) (x : Fin 10 → ℝ) (o : Fin 10) : ℝ :=
  ∑ k : Fin 10, outputGeneratorMatrix g o k * x k

set_option maxHeartbeats 0 in
theorem output_coordinates_explicit (g : Fin 7) (x : Fin 10 → ℝ) :
    outputCoordinateTransport g x = outputTransportExplicit g x := by
  funext o
  unfold outputCoordinateTransport
  rw [sum_fin_ten]
  fin_cases g <;> fin_cases o <;>
    norm_num [outputGeneratorMatrix, outputTransportExplicit] <;> ring
#print axioms output_coordinates_explicit
end
end AASCSemanticExhaustion
