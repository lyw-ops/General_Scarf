import BeyondSperner.FixedPoint.AffineBrouwer
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Brouwer's theorem on compact convex sets

This file derives Brouwer's fixed-point theorem for a nonempty compact convex
subset of an arbitrary finite-dimensional real normed space from the version
for affine simplices proved in `BeyondSperner.FixedPoint.AffineBrouwer`.

No general fixed-point theorem from Mathlib is used.
-/

namespace BeyondSperner
namespace ScarfBrouwer

open Classical Set Metric Real InnerProductSpace Module
open scoped Pointwise

noncomputable section

/-- Every compact set in a finite-dimensional real normed space is contained
in the convex hull of a full affine basis.  The construction translates an
arbitrary affine basis so that its centroid is zero and then dilates it by a
positive real unit. -/
lemma exists_affineSimplex_superset
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E}
    (hcompact : IsCompact K) :
    ∃ b : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E,
      K ⊆ affineSimplex b := by
  obtain ⟨b₀⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (finrank ℝ E + 1)) (k := ℝ) (P := E) (by simp)
  let c : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E :=
    -Finset.univ.centroid ℝ b₀ +ᵥ b₀
  have hc₀ : 0 ∈ interior (convexHull ℝ (Set.range c) : Set E) := by
    simpa [c, convexHull_vadd, interior_vadd, range_add, Pi.vadd_def,
      mem_vadd_set_iff_neg_vadd_mem]
      using b₀.centroid_mem_interior_convexHull
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (isOpen_interior.mem_nhds hc₀)
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hclosed : Metric.closedBall (0 : E) δ ⊆
      convexHull ℝ (Set.range c) := by
    calc
      Metric.closedBall (0 : E) δ ⊆ Metric.ball 0 ε := by
        apply Metric.closedBall_subset_ball
        dsimp [δ]
        linarith
      _ ⊆ interior (convexHull ℝ (Set.range c)) := hεball
      _ ⊆ convexHull ℝ (Set.range c) := interior_subset
  obtain ⟨R, hR, hKR⟩ :=
    hcompact.isBounded.subset_closedBall_lt 0 (0 : E)
  let a : ℝ := R / δ
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let u : ℝˣ := Units.mk0 a ha.ne'
  let b : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E := u • c
  refine ⟨b, ?_⟩
  intro x hx
  let y : E := a⁻¹ • x
  have hxnorm : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hKR hx
  have hynorm : ‖y‖ ≤ δ := by
    rw [show y = a⁻¹ • x by rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    rw [inv_mul_le_iff₀ ha]
    have haδ : a * δ = R := by
      simp [a, hδ.ne']
    simpa [haδ] using hxnorm
  have hy : y ∈ convexHull ℝ (Set.range c) := hclosed (by
    simpa [Metric.mem_closedBall, dist_zero_right] using hynorm)
  rw [affineSimplex]
  have hrange : Set.range b = a • Set.range c := by
    simp [b, u, Pi.smul_def, range_smul]
  rw [hrange, convexHull_smul]
  refine ⟨y, hy, ?_⟩
  exact smul_inv_smul₀ ha.ne' x

/-- A chosen nearest point in a nonempty complete convex subset of a real
inner product space. -/
noncomputable def convexNearestPoint
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H)
    (hne : C.Nonempty)
    (hcomplete : IsComplete C)
    (hconvex : Convex ℝ C)
    (x : H) : C :=
  ⟨Classical.choose
      (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x),
    (Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x)).1⟩

/-- The selected point realizes the infimum of the distances to the convex
set. -/
lemma convexNearestPoint_spec
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H)
    (hne : C.Nonempty)
    (hcomplete : IsComplete C)
    (hconvex : Convex ℝ C)
    (x : H) :
    ‖x - (convexNearestPoint C hne hcomplete hconvex x : H)‖ =
      ⨅ z : C, ‖x - z‖ := by
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x)).2

/-- Variational inequality satisfied by the selected nearest point. -/
lemma convexNearestPoint_variational
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H)
    (hne : C.Nonempty)
    (hcomplete : IsComplete C)
    (hconvex : Convex ℝ C)
    (x : H) {z : H} (hz : z ∈ C) :
    inner ℝ (x - (convexNearestPoint C hne hcomplete hconvex x : H))
      (z - (convexNearestPoint C hne hcomplete hconvex x : H)) ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hconvex
    (convexNearestPoint C hne hcomplete hconvex x).property).mp
      (convexNearestPoint_spec C hne hcomplete hconvex x) z hz

/-- Metric projection to a nonempty complete convex set is nonexpansive. -/
lemma convexNearestPoint_lipschitz
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H)
    (hne : C.Nonempty)
    (hcomplete : IsComplete C)
    (hconvex : Convex ℝ C) :
    LipschitzWith 1 (convexNearestPoint C hne hcomplete hconvex) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  let p : H := convexNearestPoint C hne hcomplete hconvex x
  let q : H := convexNearestPoint C hne hcomplete hconvex y
  change ‖p - q‖ ≤ ‖x - y‖
  have hp : p ∈ C :=
    (convexNearestPoint C hne hcomplete hconvex x).property
  have hq : q ∈ C :=
    (convexNearestPoint C hne hcomplete hconvex y).property
  have hxp : 0 ≤ inner ℝ (x - p) (p - q) := by
    have h := convexNearestPoint_variational C hne hcomplete hconvex x hq
    change inner ℝ (x - p) (q - p) ≤ 0 at h
    rw [show q - p = -(p - q) by abel, inner_neg_right] at h
    linarith
  have hqy : 0 ≤ inner ℝ (q - y) (p - q) := by
    have h := convexNearestPoint_variational C hne hcomplete hconvex y hp
    change inner ℝ (y - q) (p - q) ≤ 0 at h
    rw [show q - y = -(y - q) by abel, inner_neg_left]
    linarith
  have hlower : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by
    rw [← real_inner_self_eq_norm_sq]
    have hdecomp : x - y = (x - p) + (p - q) + (q - y) := by abel
    rw [hdecomp, inner_add_left, inner_add_left]
    linarith
  have hupper : inner ℝ (x - y) (p - q) ≤ ‖x - y‖ * ‖p - q‖ :=
    real_inner_le_norm _ _
  have hmul : ‖p - q‖ ^ 2 ≤ ‖x - y‖ * ‖p - q‖ :=
    hlower.trans hupper
  by_cases hd : p - q = 0
  · simp [hd]
  · have hdpos : 0 < ‖p - q‖ := norm_pos_iff.mpr hd
    nlinarith [hmul]

/-- Metric projection restricts to the identity on the convex set. -/
lemma convexNearestPoint_fix
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H)
    (hne : C.Nonempty)
    (hcomplete : IsComplete C)
    (hconvex : Convex ℝ C)
    {x : H} (hx : x ∈ C) :
    (convexNearestPoint C hne hcomplete hconvex x : H) = x := by
  let _ : Nonempty C := hne.to_subtype
  have hbdd : BddBelow (Set.range fun z : C ↦ ‖x - z‖) :=
    ⟨0, Set.forall_mem_range.mpr fun z ↦ norm_nonneg _⟩
  have hinf_nonneg : 0 ≤ ⨅ z : C, ‖x - z‖ :=
    le_ciInf fun z ↦ norm_nonneg _
  have hinf_le : (⨅ z : C, ‖x - z‖) ≤ 0 := by
    have hcandidate := ciInf_le hbdd (⟨x, hx⟩ : C)
    simpa using hcandidate
  have hinf : (⨅ z : C, ‖x - z‖) = 0 :=
    le_antisymm hinf_le hinf_nonneg
  have hnorm :
      ‖x - (convexNearestPoint C hne hcomplete hconvex x : H)‖ = 0 := by
    rw [convexNearestPoint_spec C hne hcomplete hconvex x, hinf]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

/-- Brouwer's theorem for compact convex subsets of finite-dimensional real
inner product spaces.  It is obtained by retracting a containing affine
simplex onto the convex set and applying the affine-simplex theorem. -/
theorem scarf_brouwer_fixedPoint_compactConvex_inner
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {C : Set H}
    (hne : C.Nonempty)
    (hcompact : IsCompact C)
    (hconvex : Convex ℝ C)
    (g : C → C)
    (hcont : Continuous g) :
    ∃ x : C, g x = x := by
  obtain ⟨b, hCS⟩ := exists_affineSimplex_superset hcompact
  let ι : C → affineSimplex b := fun x ↦ ⟨x, hCS x.property⟩
  let r : affineSimplex b → C := fun z ↦
    convexNearestPoint C hne hcompact.isComplete hconvex z.1
  let F : affineSimplex b → affineSimplex b := fun z ↦ ι (g (r z))
  have hι : Continuous ι := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hr : Continuous r :=
    (convexNearestPoint_lipschitz C hne hcompact.isComplete hconvex).continuous.comp
      continuous_subtype_val
  have hF : Continuous F := hι.comp (hcont.comp hr)
  obtain ⟨z, hz⟩ := scarf_brouwer_fixedPoint_affineSimplex b F hF
  have hzval := congrArg Subtype.val hz
  have hzunder : ((g (r z) : C) : H) = (z : H) := by
    simpa [F, ι] using hzval
  have hzC : (z : H) ∈ C := by
    rw [← hzunder]
    exact (g (r z)).property
  let x : C := ⟨z, hzC⟩
  have hrx : r z = x := by
    apply Subtype.ext
    simpa [r, x] using
      (convexNearestPoint_fix C hne hcompact.isComplete hconvex hzC)
  have hgr : g (r z) = x := by
    apply Subtype.ext
    simpa [x] using hzunder
  refine ⟨x, ?_⟩
  simpa [hrx] using hgr

/-- Brouwer's fixed-point theorem for a nonempty compact convex subset of an
arbitrary finite-dimensional real normed space. -/
theorem scarf_brouwer_fixedPoint_compactConvex
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E}
    (hne : K.Nonempty)
    (hcompact : IsCompact K)
    (hconvex : Convex ℝ K)
    (f : K → K)
    (hcont : Continuous f) :
    ∃ x : K, f x = x := by
  let H := EuclideanSpace ℝ (Fin (finrank ℝ E))
  let e : E ≃L[ℝ] H := toEuclidean
  let C : Set H := e '' K
  let eK : K ≃ₜ C := e.toHomeomorph.image K
  have hCne : C.Nonempty := by
    exact hne.image e
  have hCcompact : IsCompact C := by
    exact hcompact.image e.continuous
  have hCconvex : Convex ℝ C := by
    exact hconvex.linear_image e.toLinearEquiv.toLinearMap
  let g : C → C := fun y ↦ eK (f (eK.symm y))
  have hg : Continuous g :=
    eK.continuous.comp (hcont.comp eK.symm.continuous)
  obtain ⟨y, hy⟩ :=
    scarf_brouwer_fixedPoint_compactConvex_inner hCne hCcompact hCconvex g hg
  refine ⟨eK.symm y, ?_⟩
  apply eK.injective
  simpa [g] using hy

end

end ScarfBrouwer
end BeyondSperner
