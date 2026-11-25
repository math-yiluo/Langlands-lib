/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement

/-!
# The unit of `Lh^* ⊣ Rh_*` on extensions by zero

All schemes are separated and of finite type over a field `k` of characteristic `p > 0` with
`p ≠ ℓ`, and all morphisms are morphisms of `Over (Spec (.of k))`. Let `Λ` be a coefficient ring
and consider a cartesian square
```
X --i--> Z
|𝟙       |h
v        v
X --i₁-> Z₁
```
with `i` and `i₁` open immersions, that is `h⁻¹(X) = X`. Given a right adjoint `Rh_*` of
`Lh^* : Dᵇc(Z₁)⟦Λ⟧ ⥤ Dᵇc(Z)⟦Λ⟧` satisfying base change for this square and for the base change of
`h` along the closed complement `c : Zc ⟶ Z₁` of `i₁` (for instance `h` proper, by proper base
change), the unit `i₁_! K ⟶ Rh_* Lh^* (i₁_! K)` is an isomorphism for every `K ∈ Dᵇc(X)⟦Λ⟧`
(`ProEtale.CondensedRing.isIso_unit_app_openImmersionLowerShriek`).

## Proof

The restrictions `Li₁^*` and `Lc^*` jointly reflect isomorphisms
(`ProEtale.CondensedRing.isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl`).

* Over `X`: the restriction `Li₁^*` of the unit, followed by the base-change morphism
  `Li₁^* Rh_* ⟶ R𝟙_* Li^*`, is the unit of `L𝟙^* ⊣ R𝟙_*` followed by the pullback comparison,
  by the triangle identity; the unit of `L𝟙^* ⊣ R𝟙_*` is an isomorphism, `L𝟙^*` being isomorphic
  to the identity.
* Over `Zc`: both sides vanish. `Lc^* i₁_! = 0` since `Zc` misses `X`, and by base change along
  `c`, `Lc^* Rh_* Lh^* (i₁_! K) ≅ Rq_* Lc'^* Lh^* (i₁_! K)`, where `c' : Zc' ⟶ Z` is the base change
  of `c`; it vanishes since `c' ≫ h` factors through `c`.
-/

@[expose] public section

universe u

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']

/-- If the exchange morphism `Rf ⋙ G ⟶ G' ⋙ Rf'` of `θ : G ⋙ Lf' ≅ Lf ⋙ G'` is an isomorphism
and the unit of `Lf' ⊣ Rf'` is an isomorphism, then `G` inverts the unit of `Lf ⊣ Rf`: by the
triangle identity, `G (η N)` followed by the exchange morphism at `Lf N` is the unit of
`Lf' ⊣ Rf'` followed by `Rf' (θ N)`. -/
lemma isIso_map_unit_app_of_isIso_exchangeRight {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'}
    {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') [IsIso af'.unit] [IsIso (exchangeRight af af' θ)] (N : B) :
    IsIso (G.map (af.unit.app N)) := by
  have key : G.map (af.unit.app N) ≫ (exchangeRight af af' θ).app (Lf.obj N) =
      af'.unit.app (G.obj N) ≫ Rf'.map (θ.hom.app N) := by
    have hu := af'.unit.naturality (G.map (af.unit.app N))
    simp only [Functor.id_map, Functor.comp_map] at hu
    rw [exchangeRight_app, reassoc_of% hu, ← Rf'.map_comp, ← Rf'.map_comp]
    refine congrArg (af'.unit.app _ ≫ ·) (congrArg Rf'.map ?_)
    have hθ := θ.hom.naturality (af.unit.app N)
    simp only [Functor.comp_map, Functor.comp_obj] at hθ
    rw [← Category.assoc, hθ, Category.assoc, ← G'.map_comp]
    simp
  have : IsIso (G.map (af.unit.app N) ≫ (exchangeRight af af' θ).app (Lf.obj N)) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((exchangeRight af af' θ).app (Lf.obj N))

end CategoryTheory.Adjunction

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]
  [IsProper h.left]

omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] [IsProper h.left] in
/-- Over the open `X`: if the base-change morphism `Li₁^* Rh_* ⟶ R𝟙_* Li^*` of the square is an
isomorphism, the restriction to `X` of the unit of `Lh^* ⊣ Rh_*` is an isomorphism. -/
lemma isIso_upperStar_map_unit_app_of_isIso {Rh : Dᵇc(Z.left)⟦Λ⟧ ⥤ Dᵇc(Z₁.left)⟦Λ⟧}
    (adj : boundedConstructibleUpperStar Λ ℓ h ⊣ Rh) {R₁ : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧}
    (adj₁ : boundedConstructibleUpperStar Λ ℓ (𝟙 X) ⊣ R₁) (sq : IsPullback (𝟙 X) i i₁ h)
    (hbc : IsIso (Adjunction.exchangeRight adj adj₁
      (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip.toCommSq)))
    (N : Dᵇc(Z₁.left)⟦Λ⟧) :
    IsIso ((boundedConstructibleUpperStar Λ ℓ i₁).map (adj.unit.app N)) := by
  have : (boundedConstructibleUpperStar Λ ℓ (𝟙 X)).Full :=
    Functor.Full.of_iso (boundedConstructibleUpperStarId Λ ℓ X).symm
  have : (boundedConstructibleUpperStar Λ ℓ (𝟙 X)).Faithful :=
    Functor.Faithful.of_iso (boundedConstructibleUpperStarId Λ ℓ X).symm
  exact Adjunction.isIso_map_unit_app_of_isIso_exchangeRight adj adj₁
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip.toCommSq) N

omit [IsOpenImmersion i.left] in
/-- **The unit of `Lh^* ⊣ Rh_*` on extensions by zero**: for a cartesian square of open
immersions `i`, `i₁` and a proper `h`, if `Rh_*` satisfies base change for this square and for the
base change of `h` along the closed complement of `i₁`, then the unit
`i₁_! K ⟶ Rh_* Lh^* (i₁_! K)` is an isomorphism. -/
theorem isIso_unit_app_openImmersionLowerShriek {Rh : Dᵇc(Z.left)⟦Λ⟧ ⥤ Dᵇc(Z₁.left)⟦Λ⟧}
    (adj : boundedConstructibleUpperStar Λ ℓ h ⊣ Rh) {R₁ : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧}
    (adj₁ : boundedConstructibleUpperStar Λ ℓ (𝟙 X) ⊣ R₁)
    {Rq : Dᵇc((overPullbackObj h (overClosedComplement i₁)).left)⟦Λ⟧ ⥤
      Dᵇc((overClosedComplementObj i₁).left)⟦Λ⟧}
    (adjq : boundedConstructibleUpperStar Λ ℓ (overPullbackSnd h (overClosedComplement i₁)) ⊣ Rq)
    (sq : IsPullback (𝟙 X) i i₁ h)
    (h₁ : IsIso (Adjunction.exchangeRight adj adj₁
      (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip.toCommSq)))
    (h₂ : IsIso (Adjunction.exchangeRight adj adjq
      (boundedConstructiblePullbackSquareComparison Λ ℓ
        (isPullback_overPullbackFst_overPullbackSnd h (overClosedComplement i₁)).toCommSq)))
    (K : Dᵇc(X.left)⟦Λ⟧) :
    IsIso (adj.unit.app ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)) := by
  have : QuasiCompact (i₁.left ≫ Z₁.hom) := by
    rw [Over.w i₁]
    infer_instance
  have : QuasiCompact i₁.left := QuasiCompact.of_comp i₁.left Z₁.hom
  let c := overClosedComplement i₁
  let c' := overPullbackFst h c
  let q := overPullbackSnd h c
  refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl Λ ℓ c i₁
    (isCompl_range_overClosedComplement i₁) _
    (isIso_upperStar_map_unit_app_of_isIso Λ ℓ adj adj₁ sq h₁ _) ?_
  -- Over the closed complement both sides vanish.
  have hS : IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)) :=
    isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ i₁ c
      (isCompl_range_overClosedComplement i₁).disjoint.symm K
  have hdisj : Disjoint (Set.range i₁.left.base) (Set.range (c' ≫ h).left.base) := by
    rw [(isPullback_overPullbackFst_overPullbackSnd h c).w]
    refine (isCompl_range_overClosedComplement i₁).disjoint.symm.mono_right ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨q.left.base x, rfl⟩
  have hc' : IsZero ((boundedConstructibleUpperStar Λ ℓ c').obj
      ((boundedConstructibleUpperStar Λ ℓ h).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))) :=
    (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ i₁ (c' ≫ h) hdisj
      K).of_iso ((boundedConstructibleUpperStarComp Λ ℓ c' h).app _).symm
  have : Rq.PreservesZeroMorphisms := by
    have := adjq.isRightAdjoint
    exact Functor.preservesZeroMorphisms_of_isRightAdjoint Rq
  have hT : IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
      (Rh.obj ((boundedConstructibleUpperStar Λ ℓ h).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)))) :=
    (Rq.map_isZero hc').of_iso (asIso ((Adjunction.exchangeRight adj adjq
      (boundedConstructiblePullbackSquareComparison Λ ℓ
        (isPullback_overPullbackFst_overPullbackSnd h c).toCommSq)).app _))
  exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
