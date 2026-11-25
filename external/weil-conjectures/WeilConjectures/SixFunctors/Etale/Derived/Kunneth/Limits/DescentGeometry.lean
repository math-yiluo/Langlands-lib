/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Descent of pointed étale neighbourhoods along a limit of schemes

Let `X = lim Xᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, with projections `pᵢ : X ⟶ Xᵢ`, and let `x̄ : Spec Ω ⟶ X` be a point.

- `AlgebraicGeometry.exists_etale_descent_of_isLimit`: every pointed étale neighbourhood
  `(W, w)` of `x̄` is refined by the base change `(V ×_{Xᵢ} X, (v, x̄))` of a pointed étale
  neighbourhood `(V, v)` of `pᵢ x̄` at some stage.
- `AlgebraicGeometry.exists_etale_hom_descent_of_isLimit`: given moreover a morphism
  `φ : W ⟶ V ×_{Xᵢ} X` over `X`, the pointed neighbourhood `(W, w)` is refined by the base
  change of a pointed étale neighbourhood `(V', v')` of `pⱼ x̄` at a later stage `j ⟶ i`, in
  such a way that the composite with `φ` comes from a morphism `V' ⟶ V ×_{Xᵢ} Xⱼ` over `Xⱼ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A pointed scheme `(W, w)` over `S` has an affine open neighbourhood `W'` of `w` mapping into
an affine open `N` of `S`. -/
lemma exists_isAffineOpen_range_subset {Ω : Type u} [Field Ω] {S W : Scheme.{u}} (a : W ⟶ S)
    (w : Spec (.of Ω) ⟶ W) :
    ∃ (W' : W.Opens) (N : S.Opens), IsAffineOpen W' ∧ IsAffineOpen N ∧
      Set.range (W'.ι ≫ a) ⊆ (N : Set S) ∧ Set.range w ⊆ (W' : Set W) := by
  let p : Spec (.of Ω) := default
  obtain ⟨N, hN, hpN, -⟩ := exists_isAffineOpen_mem_and_subset (x := a (w p))
    (U := ⊤) trivial
  obtain ⟨W', hW', hpW', hsub⟩ := exists_isAffineOpen_mem_and_subset (x := w p)
    (U := a ⁻¹ᵁ N) hpN
  refine ⟨W', N, hW', hN, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hsub y.2
  · rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y p]

section Descent

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **Descent of pointed étale neighbourhoods.** Every pointed étale neighbourhood `(W, w)` of
a point `x̄` of `X = lim Xᵢ` is refined by the base change `(V ×_{Xᵢ} X, (v, x̄))` of a pointed
étale neighbourhood `(V, v)` of `pᵢ x̄` at some stage `i`. -/
lemma exists_etale_descent_of_isLimit {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ c.pt)
    {W : Scheme.{u}} (a : W ⟶ c.pt) [Etale a] (w : Spec (.of Ω) ⟶ W) (hw : w ≫ a = x) :
    ∃ (i : I) (V : Scheme.{u}) (b : V ⟶ D.obj i) (_ : Etale b) (v : Spec (.of Ω) ⟶ V)
      (hv : v ≫ b = x ≫ c.π.app i) (φ : pullback b (c.π.app i) ⟶ W),
      φ ≫ a = pullback.snd _ _ ∧ pullback.lift v x hv ≫ φ = w := by
  obtain ⟨W', N, hW', hN, hWN, hw'⟩ := exists_isAffineOpen_range_subset a w
  have : IsAffine W' := hW'
  let w' : Spec (.of Ω) ⟶ W' := IsOpenImmersion.lift W'.ι w (by simpa using hw')
  have hw'ι : w' ≫ W'.ι = w := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨i, Y, hY, p, hp, h, H⟩ :=
    Scheme.exists_isPullback_of_etale_of_isAffineOpen D c hc (W'.ι ≫ a) hN hWN
  have hv : (w' ≫ h) ≫ p = x ≫ c.π.app i := by
    rw [Category.assoc, H.w, ← Category.assoc, ← Category.assoc, hw'ι, hw]
  refine ⟨i, Y, p, hp, w' ≫ h, hv, H.isoPullback.inv ≫ W'.ι, ?_, ?_⟩
  · rw [Category.assoc, H.isoPullback_inv_snd]
  · have e : pullback.lift (w' ≫ h) x hv = w' ≫ H.isoPullback.hom := by
      apply pullback.hom_ext
      · simp
      · simp [reassoc_of% hw'ι, hw]
    rw [e, Category.assoc, Iso.hom_inv_id_assoc, hw'ι]

include hc in
/-- **Descent of morphisms of pointed étale neighbourhoods.** Let `(V, v)` be an étale scheme
over a stage `Xᵢ`, and let `φ : W ⟶ V ×_{Xᵢ} X` be a morphism over `X` from an étale `X`-scheme
`W` with a point `w` over `x̄`. Then there are `j ⟶ i`, an étale `Xⱼ`-scheme `V'` with a point
`v'` over `pⱼ x̄`, a morphism `ψ : V' ⟶ V ×_{Xᵢ} Xⱼ` over `Xⱼ` compatible with the points, and a
morphism `χ : V' ×_{Xⱼ} X ⟶ W` over `X` sending `(v', x̄)` to `w`, such that `φ ∘ χ` is the base
change of `ψ` (on the first components). -/
lemma exists_etale_hom_descent_of_isLimit [∀ i, CompactSpace (D.obj i)] {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ c.pt) {i : I} {V : Scheme.{u}} (b : V ⟶ D.obj i) [Etale b]
    {W : Scheme.{u}} (a : W ⟶ c.pt) [Etale a] (φ : W ⟶ pullback b (c.π.app i))
    (hφ : φ ≫ pullback.snd _ _ = a) (w : Spec (.of Ω) ⟶ W) (hw : w ≫ a = x) :
    ∃ (j : I) (f : j ⟶ i) (V' : Scheme.{u}) (b' : V' ⟶ D.obj j) (_ : Etale b')
      (v' : Spec (.of Ω) ⟶ V') (hv' : v' ≫ b' = x ≫ c.π.app j)
      (ψ : V' ⟶ pullback b (D.map f)) (χ : pullback b' (c.π.app j) ⟶ W),
      ψ ≫ pullback.snd _ _ = b' ∧
      v' ≫ ψ ≫ pullback.fst _ _ = w ≫ φ ≫ pullback.fst _ _ ∧
      χ ≫ a = pullback.snd _ _ ∧ pullback.lift v' x hv' ≫ χ = w ∧
      χ ≫ φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ψ ≫ pullback.fst _ _ := by
  obtain ⟨W', N, hW', hN, hWN, hw'⟩ := exists_isAffineOpen_range_subset a w
  have : IsAffine W' := hW'
  let w' : Spec (.of Ω) ⟶ W' := IsOpenImmersion.lift W'.ι w (by simpa using hw')
  have hw'ι : w' ≫ W'.ι = w := IsOpenImmersion.lift_fac _ _ _
  -- restrict the diagram to the stages over `i`
  let D' := Over.forget i ⋙ D
  let c' : Cone D' := c.whisker (Over.forget i)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have (k k' : Over i) (f : k ⟶ k') : IsAffineHom (D'.map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left))
  have (k : Over i) : QuasiSeparatedSpace (D'.obj k) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj k.left))
  have (k : Over i) : CompactSpace (D'.obj k) := inferInstanceAs (CompactSpace (D.obj k.left))
  obtain ⟨k, Y, hY, p, hp, h, H⟩ :=
    Scheme.exists_isPullback_of_etale_of_isAffineOpen D' c' hc' (W'.ι ≫ a) hN hWN
  let π : D' ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app k := D.map k.hom
      naturality k k' f := by
        simp [D', ← D.map_comp] }
  obtain ⟨m, f', ψ₀, hψ₀, hψ₀'⟩ := Scheme.exists_isPullbackLift_comp_eq hc' π H b
    (W'.ι ≫ φ ≫ pullback.fst _ _) (by
      simp only [Category.assoc, pullback.condition]
      rw [reassoc_of% hφ]
      simp [c', π, c.w])
  let b' : pullback p (D'.map f') ⟶ D.obj m.left := pullback.snd _ _
  have hψ : ψ₀ ≫ b = b' ≫ D.map m.hom := hψ₀
  let L := isPullbackLift D' c' f' H
  have H' : IsPullback L (W'.ι ≫ a) b' (c.π.app m.left) := isPullback_isPullbackLift f' H
  have hv' : (w' ≫ L) ≫ b' = x ≫ c.π.app m.left := by
    rw [Category.assoc, H'.w, ← Category.assoc, ← Category.assoc, hw'ι, hw]
  have hL : L ≫ ψ₀ = W'.ι ≫ φ ≫ pullback.fst _ _ := hψ₀'
  refine ⟨m.left, m.hom, _, b', inferInstance, w' ≫ L, hv', pullback.lift ψ₀ b' hψ,
    H'.isoPullback.inv ≫ W'.ι, by simp, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]
    erw [pullback.lift_fst]
    rw [hL, reassoc_of% hw'ι]
  · rw [Category.assoc, H'.isoPullback_inv_snd]
  · have e : pullback.lift (w' ≫ L) x hv' = w' ≫ H'.isoPullback.hom := by
      apply pullback.hom_ext
      · simp
      · simp [reassoc_of% hw'ι, hw]
    rw [e, Category.assoc, Iso.hom_inv_id_assoc, hw'ι]
  · rw [pullback.lift_fst, Category.assoc, ← hL, H'.isoPullback_inv_fst_assoc]

end Descent

end AlgebraicGeometry
