import BeyondSperner.Geometry.Triangulation.Applications
import FormalizationInterface.VectorHedgehogIntersection
import FormalizationInterface.InwardTangentIntersection

/-!
# Arbitrary geometric triangulations through the intersection route

These wrappers instantiate the already proved geometric triangulation
obligations with the paper-route versions of Theorems 10.9 and 10.10.  They
have the same mathematical conclusions as `exists_fullSimplex_mem_convexHull_colorPoints_of_isVectorHedgehogColoring` and
`exists_fullSimplex_zero_mem_convexHull_colorPoints_of_isInwardTangentColoring`, but their Theorem 10.8 dependency is the independent
intersection/general-position proof.
-/

namespace BeyondSperner
namespace GeometricTriangulation
namespace Intersection

open Classical Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ E)
variable (T : Data b)

/-- Theorem 10.9 for an arbitrary finite geometric triangulation, routed
through the paper's intersection proof of Theorem 10.8. -/
theorem exists_fullSimplex_mem_convexHull_colorPoints_of_isVectorHedgehogColoring
    (c : (family b T).Vertex → E)
    (hhedgehog : AffineColoring.IsVectorHedgehogColoring
      (family b T) b (fun v ↦ v.1.1) c)
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b)) :
    ∃ sigma : Finset T.Vertex,
      ∃ hsigma : sigma ∈ (family b T).complex Finset.univ,
        sigma.card = n + 1 ∧
          z ∈ convexHull ℝ
            (AffineColoring.affineSimplexColorPoints
              (family b T) c Finset.univ sigma hsigma : Set E) := by
  let _ : FiniteDimensional ℝ E := b.finiteDimensional
  exact AffineColoring.Intersection.exists_fullSimplex_mem_convexHull_colorPoints_of_isVectorHedgehogColoring (family b T) b
    (fun v ↦ v.1.1) c ((isNonbranching b T).isChainSimplex b T)
    (family_face_coordinate b T) hhedgehog z hz

/-- Theorem 10.10 for an arbitrary finite geometric triangulation, routed
through the paper's intersection proof of Theorem 10.8. -/
theorem exists_fullSimplex_zero_mem_convexHull_colorPoints_of_isInwardTangentColoring
    (hb : AffineColoring.IsCenteredAffineBasis b)
    (c : (family b T).Vertex → E)
    (hinward : AffineColoring.IsInwardTangentColoring
      (family b T) b (fun v ↦ v.1.1) c) :
    ∃ sigma : Finset T.Vertex,
      ∃ hsigma : sigma ∈ (family b T).complex Finset.univ,
        sigma.card = n + 1 ∧
          (0 : E) ∈ convexHull ℝ
          (AffineColoring.affineSimplexColorPoints
              (family b T) c Finset.univ sigma hsigma : Set E) := by
  let _ : FiniteDimensional ℝ E := b.finiteDimensional
  have hPure :
      ((family b T).complex Finset.univ).IsPureOfCardinality
        (Fintype.card (Fin (n + 1))) := by
    simpa using family_full_isPure_of_data b T
  obtain ⟨sigma, hsigma, hcard, hzero⟩ :=
    AffineColoring.Intersection.exists_fullSimplex_zero_mem_convexHull_colorPoints_of_isInwardTangentColoring (family b T) b hb
      (fun v ↦ v.1.1) c ((isNonbranching b T).isChainSimplex b T)
      (family_face_coordinate b T) hinward
      (family_subset_full b T) hPure
  refine ⟨sigma, hsigma, ?_, hzero⟩
  simpa using hcard

end Intersection
end GeometricTriangulation
end BeyondSperner
