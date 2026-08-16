import BeyondSperner.FixedPoint.Kakutani
import BeyondSperner.FixedPoint.CompactConvexBrouwer
import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Kakutani's theorem on compact convex sets

This file transports the Scarf--Kakutani theorem from the standard simplex
to a nonempty compact convex subset of an arbitrary finite-dimensional real
normed space.  The inner-product-space proof uses an enclosing affine
simplex and metric projection; the general result follows by transport to a
Euclidean space.

No general fixed-point theorem from Mathlib is used.
-/

namespace BeyondSperner
namespace KakutaniScarf

open Classical Filter Set
open ScarfBrouwer
open scoped Topology

noncomputable section

/-- Kakutani's fixed-point theorem for a compact convex subset of a
finite-dimensional real inner-product space, in closed-graph form. -/
theorem scarf_kakutani_fixedPoint_compactConvex_inner
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    {C : Set H}
    (hne : C.Nonempty)
    (hcompact : IsCompact C)
    (hconvex : Convex ℝ C)
    (Φ : C → Set H)
    (hΦne : ∀ x, (Φ x).Nonempty)
    (hΦC : ∀ x, Φ x ⊆ C)
    (hΦconvex : ∀ x, Convex ℝ (Φ x))
    (hΦclosed : IsClosed {q : C × H | q.2 ∈ Φ q.1}) :
    ∃ x : C, (x : H) ∈ Φ x := by
  let I := Fin (Module.finrank ℝ H + 1)
  obtain ⟨b, hCS⟩ := ScarfBrouwer.exists_affineSimplex_superset hcompact
  let A : (I → ℝ) →ᵃ[ℝ] H := Finset.univ.affineCombination ℝ b
  let p : (I → ℝ) → C := fun u ↦
    ScarfBrouwer.convexNearestPoint
      C hne hcompact.isComplete hconvex (A u)
  have hA : Continuous A := A.continuous_of_finiteDimensional
  have hp : Continuous p :=
    (ScarfBrouwer.convexNearestPoint_lipschitz
      C hne hcompact.isComplete hconvex).continuous.comp hA
  let ψ : (I → ℝ) → Set (I → ℝ) := fun u ↦
    ScarfBrouwer.standardSimplex ∩ A ⁻¹' Φ (p u)
  let Khat : Correspondence I := {
    value := ψ
    nonempty_value := by
      intro u _hu
      obtain ⟨y, hy⟩ := hΦne (p u)
      have hyC : y ∈ C := hΦC (p u) hy
      let v : I → ℝ := ScarfBrouwer.affineCoordinateMap b y
      refine ⟨v, ?_, ?_⟩
      · exact (ScarfBrouwer.affineCoordinateMap_mem_standardSimplex_iff b y).2
          (hCS hyC)
      · have hAv : A v = y := by
          simp [A, v]
        simpa [hAv] using hy
    value_subset := by
      intro u _hu v hv
      exact hv.1
    convex_value := by
      intro u
      have hsimplex : Convex ℝ
          (ScarfBrouwer.standardSimplex : Set (I → ℝ)) := by
        change Convex ℝ (stdSimplex ℝ I)
        exact convex_stdSimplex ℝ I
      exact hsimplex.inter ((hΦconvex (p u)).affine_preimage A)
    isClosed_graph := by
      have hsimplex : IsClosed
          (ScarfBrouwer.standardSimplex : Set (I → ℝ)) := by
        change IsClosed (stdSimplex ℝ I)
        exact isClosed_stdSimplex ℝ I
      have hsnd : IsClosed
          {q : (I → ℝ) × (I → ℝ) |
            q.2 ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ))} :=
        hsimplex.preimage continuous_snd
      let T : ((I → ℝ) × (I → ℝ)) → C × H := fun q ↦
        (p q.1, A q.2)
      have hT : Continuous T :=
        (hp.comp continuous_fst).prodMk (hA.comp continuous_snd)
      have hpre : IsClosed
          (T ⁻¹' {q : C × H | q.2 ∈ Φ q.1}) :=
        hΦclosed.preimage hT
      have hgraph :
          {q : (I → ℝ) × (I → ℝ) | q.2 ∈ ψ q.1} =
            {q : (I → ℝ) × (I → ℝ) |
              q.2 ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ))} ∩
              T ⁻¹' {q : C × H | q.2 ∈ Φ q.1} := by
        ext q
        simp [ψ, T]
      rw [hgraph]
      exact hsnd.inter hpre }
  obtain ⟨u, _hu, huψ⟩ := KakutaniScarf.kakutani_fixedPoint Khat
  have hxC : A u ∈ C := hΦC (p u) huψ.2
  let x : C := ⟨A u, hxC⟩
  have hpx : p u = x := by
    apply Subtype.ext
    simpa [p, x] using
      (ScarfBrouwer.convexNearestPoint_fix
        C hne hcompact.isComplete hconvex hxC)
  refine ⟨x, ?_⟩
  change A u ∈ Φ x
  rw [← hpx]
  exact huψ.2

/-- Kakutani's fixed-point theorem for a compact convex subset of an
arbitrary finite-dimensional real normed space, in closed-graph form. -/
theorem scarf_kakutani_fixedPoint_compactConvex
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E}
    (hne : K.Nonempty)
    (hcompact : IsCompact K)
    (hconvex : Convex ℝ K)
    (Φ : K → Set E)
    (hΦne : ∀ x, (Φ x).Nonempty)
    (hΦK : ∀ x, Φ x ⊆ K)
    (hΦconvex : ∀ x, Convex ℝ (Φ x))
    (hΦclosed : IsClosed {q : K × E | q.2 ∈ Φ q.1}) :
    ∃ x : K, (x : E) ∈ Φ x := by
  let H := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e : E ≃L[ℝ] H := toEuclidean
  let C : Set H := e '' K
  let eK : K ≃ₜ C := e.toHomeomorph.image K
  let Ψ : C → Set H := fun y ↦ e '' Φ (eK.symm y)
  have hCne : C.Nonempty := hne.image e
  have hCcompact : IsCompact C := hcompact.image e.continuous
  have hCconvex : Convex ℝ C :=
    hconvex.linear_image e.toLinearEquiv.toLinearMap
  have hΨne (y : C) : (Ψ y).Nonempty := by
    exact (hΦne (eK.symm y)).image e
  have hΨC (y : C) : Ψ y ⊆ C := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w, hΦK (eK.symm y) hw, rfl⟩
  have hΨconvex (y : C) : Convex ℝ (Ψ y) := by
    exact (hΦconvex (eK.symm y)).linear_image
      e.toLinearEquiv.toLinearMap
  let Q : C × H → K × E := fun q ↦
    (eK.symm q.1, e.symm q.2)
  have hQ : Continuous Q :=
    (eK.symm.continuous.comp continuous_fst).prodMk
      (e.symm.continuous.comp continuous_snd)
  have hgraph :
      {q : C × H | q.2 ∈ Ψ q.1} =
        Q ⁻¹' {q : K × E | q.2 ∈ Φ q.1} := by
    ext q
    constructor
    · rintro ⟨w, hw, hwq⟩
      change e.symm q.2 ∈ Φ (eK.symm q.1)
      simpa [← hwq] using hw
    · intro hq
      change e.symm q.2 ∈ Φ (eK.symm q.1) at hq
      exact ⟨e.symm q.2, hq, e.apply_symm_apply q.2⟩
  have hΨclosed : IsClosed {q : C × H | q.2 ∈ Ψ q.1} := by
    rw [hgraph]
    exact hΦclosed.preimage hQ
  obtain ⟨y, hy⟩ :=
    scarf_kakutani_fixedPoint_compactConvex_inner
      hCne hCcompact hCconvex Ψ hΨne hΨC hΨconvex hΨclosed
  rcases hy with ⟨x, hx, hxy⟩
  have hxeq : x = (eK.symm y : E) := by
    apply e.injective
    rw [hxy]
    calc
      (y : H) = ((eK (eK.symm y) : C) : H) :=
        congrArg Subtype.val (eK.apply_symm_apply y).symm
      _ = e (eK.symm y : E) := by
        exact Homeomorph.image_apply_coe e.toHomeomorph K (eK.symm y)
  subst x
  exact ⟨eK.symm y, hx⟩

/-- The textbook compact-valued upper-hemicontinuous form of Kakutani's
fixed-point theorem. -/
theorem kakutani_fixedPoint_compactConvex_of_upperHemicontinuous
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E}
    (hne : K.Nonempty)
    (hcompact : IsCompact K)
    (hconvex : Convex ℝ K)
    (Φ : K → Set E)
    (hΦne : ∀ x, (Φ x).Nonempty)
    (hΦK : ∀ x, Φ x ⊆ K)
    (hΦcompact : ∀ x, IsCompact (Φ x))
    (hΦconvex : ∀ x, Convex ℝ (Φ x))
    (hΦuhc : UpperHemicontinuous Φ) :
    ∃ x : K, (x : E) ∈ Φ x := by
  have hΦclosed : IsClosed {q : K × E | q.2 ∈ Φ q.1} := by
    apply IsSeqClosed.isClosed
    intro q z hq hz
    have hx : Tendsto (fun n ↦ (q n).1) atTop (𝓝 z.1) :=
      continuous_fst.continuousAt.tendsto.comp hz
    have hy : Tendsto (fun n ↦ (q n).2) atTop (𝓝 z.2) :=
      continuous_snd.continuousAt.tendsto.comp hz
    exact UpperHemicontinuousAt.mem_of_tendsto (hΦuhc z.1)
      (hΦcompact z.1).isClosed hx
      (Eventually.frequently (Eventually.of_forall hq)) hy
  exact scarf_kakutani_fixedPoint_compactConvex
    hne hcompact hconvex Φ hΦne hΦK hΦconvex hΦclosed

end

end KakutaniScarf
end BeyondSperner
