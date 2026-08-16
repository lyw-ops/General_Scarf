import BeyondSperner.Coloring.VectorHedgehog
import FormalizationInterface.AffineSolutionIntersection

/-!
# Theorem 10.9 through the intersection proof of Theorem 10.8

This compatibility module is outside the mathematical source tree.  It
instantiates the provider-parameterized proof in `VectorHedgehog` with
`exists_isAffineSolution`, and therefore threads the paper's Section 10
intersection route through both the strict-interior and boundary cases of
Theorem 10.9.
-/

namespace BeyondSperner
namespace AffineColoring
namespace Intersection

open Classical Set

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The strict-interior part of Theorem 10.9 using the paper-route proof of
Theorem 10.8. -/
theorem exists_fullSimplex_mem_convexHull_colorPoints_of_isStrictInteriorPoint {n : ℕ}
    (D : SimplexFamily (Fin (n + 1)) V)
    (b : AffineBasis (Fin (n + 1)) ℝ E)
    (p c : D.Vertex → E)
    (hchain : D.IsChainSimplex)
    (hface : ∀ (C : Finset (Fin (n + 1))) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hhedgehog : IsVectorHedgehogColoring D b p c)
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b))
    (hzInterior : IsStrictInteriorPoint b z) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = n + 1 ∧
        z ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set E) := by
  exact exists_fullSimplex_mem_convexHull_colorPoints_of_isStrictInteriorPoint_of_solution_provider D b p c hface hhedgehog
    (fun b' q hq ↦ exists_isAffineSolution D b' c q hq hchain)
    z hz hzInterior

/-- The full Theorem 10.9, including boundary targets, with Theorem 10.8
supplied by the paper's intersection-number/general-position proof. -/
theorem exists_fullSimplex_mem_convexHull_colorPoints_of_isVectorHedgehogColoring {n : ℕ}
    (D : SimplexFamily (Fin (n + 1)) V)
    (b : AffineBasis (Fin (n + 1)) ℝ E)
    (p c : D.Vertex → E)
    (hchain : D.IsChainSimplex)
    (hface : ∀ (C : Finset (Fin (n + 1))) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hhedgehog : IsVectorHedgehogColoring D b p c)
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b)) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = n + 1 ∧
        z ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set E) := by
  exact exists_fullSimplex_mem_convexHull_colorPoints_of_interior_cover D b c
    (fun q hq hqInterior ↦
      exists_fullSimplex_mem_convexHull_colorPoints_of_isStrictInteriorPoint D b p c hchain hface hhedgehog
        q hq hqInterior) z hz

end Intersection
end AffineColoring
end BeyondSperner
