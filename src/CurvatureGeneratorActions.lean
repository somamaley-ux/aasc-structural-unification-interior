import CurvatureGeneratorTransport
import CurvatureGeneratorTransport1
import CurvatureGeneratorTransport2
import CurvatureGeneratorTransport3
import CurvatureGeneratorTransport4
import CurvatureGeneratorTransport5
import CurvatureGeneratorTransport6

namespace AASCSemanticExhaustion
theorem curvature_generator_transport (g : Fin 7) (x : Fin 20 → ℝ) :
    pullbackFour (comparisonGenerator g).forward (curvatureEncode x) =
      curvatureEncode (curvatureCoordinateTransport g x) := by
  fin_cases g
  · exact curvature_generator_transport_0 x
  · exact curvature_generator_transport_1 x
  · exact curvature_generator_transport_2 x
  · exact curvature_generator_transport_3 x
  · exact curvature_generator_transport_4 x
  · exact curvature_generator_transport_5 x
  · exact curvature_generator_transport_6 x
#print axioms curvature_generator_transport
end AASCSemanticExhaustion
