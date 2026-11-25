/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingPieces
public import WeilConjectures.TraceFormula.OpenPieceTriangle

/-!

# The open piece coefficient of a correspondence and the counit

Let `c = (c₁, c₂)` be an endocorrespondence of `(X, K)` with coefficient map
`u : Lc₂^* K ⟶ Rc₁^! K`, and let `j : X ∖ {x} ⟶ X` be the open complement of a rational point
with `c₂⁻¹(X ∖ {x}) ⊆ c₁⁻¹(X ∖ {x})`. The open piece coefficient
`u^U : Lc₂^* j_! Lj^* K ⟶ Rc₁^! j_! Lj^* K` is compatible with the counit `ε : j_! Lj^* K ⟶ K`:
```
Rc₁^! ε ∘ u^U = u ∘ Lc₂^* ε.
```
This is the first square of the morphism of open–closed triangles induced by `u` (blueprint
`proposition-additivity-trace-classes--2`, proof of item 1, step (a)).

* `ProEtale.CondensedRing.Correspondence.pointOpenPieceCoeff_comp_map_counit`: the statement.
  Both sides are maps out of `j_{V!} Lc_{2,V}^* Lj^* K` after the open base change
  (`ProEtale.CondensedRing.map_counit_comp_eq_openSquareExchange_hom_comp`); their
  `j_{V!} ⊣ Lj_V^*` adjoints agree since the unit `Lj^* K ⟶ Lj^* j_! Lj^* K` in
  `pointOpenRestriction` is cancelled by `Lj^* ε` (triangle identity).
* `boundedConstructibleUpperShriekOpenRestrict_hom_app_comp_map_unit_comp_inv_app_comp_map`:
  the compatibility of the restriction `Lj_W^* Rg^! ≅ Rg_W^! Lj^*` with the triangle identity.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

/-- A natural isomorphism `θ : F ⋙ G ≅ H ⋙ F'` is compatible with the triangle identity of an
adjunction `L ⊣ H`: the composite
```
G (F K) --θ--> F' (H K) --F' η--> F' (H (L (H K))) --θ⁻¹--> G (F (L (H K))) --G (F ε)--> G (F K)
```
is the identity. -/
lemma iso_hom_app_comp_map_unit_comp_iso_inv_app_comp_map_map_counit {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] {L : B ⥤ A} {H : A ⥤ B}
    {F : A ⥤ C} {G : C ⥤ D} {F' : B ⥤ D} (adj : L ⊣ H) (θ : F ⋙ G ≅ H ⋙ F') (K : A) :
    (θ.hom.app K ≫ F'.map (adj.unit.app (H.obj K)) ≫ θ.inv.app (L.obj (H.obj K))) ≫
        G.map (F.map (adj.counit.app K)) =
      𝟙 (G.obj (F.obj K)) := by
  have h := θ.inv.naturality (adj.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h
  rw [Category.assoc, Category.assoc, ← h, ← Functor.map_comp_assoc,
    Adjunction.right_triangle_components, Functor.map_id,
    Category.id_comp]
  exact θ.hom_inv_id_app K

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {V W Y : Over (Spec (.of k))}
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] [LocallyOfFiniteType W.hom]
  [QuasiCompact W.hom] [IsSeparated W.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- Transporting a retraction `T ≫ Lq^* ψ = 𝟙` along `L(p ≫ q)^* ≅ Lp^* Lq^*` and an equation
`p ≫ q = j'` gives a retraction for `Lj'^* ψ`. -/
lemma eqToHom_comp_upperStarComp_hom_app_comp_map_comp_eq_id {p : V ⟶ W} {q : W ⟶ Y}
    {j' : V ⟶ Y} (h : p ≫ q = j') {M N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (T : (boundedConstructibleUpperStar _ ℓ q).obj M ⟶ (boundedConstructibleUpperStar _ ℓ q).obj N)
    (ψ : N ⟶ M) (hT : T ≫ (boundedConstructibleUpperStar _ ℓ q).map ψ = 𝟙 _) :
    eqToHom (by rw [h]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p q).hom.app M ≫
        (boundedConstructibleUpperStar _ ℓ p).map T ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p q).inv.app N ≫
        eqToHom (by rw [h]) ≫ (boundedConstructibleUpperStar _ ℓ j').map ψ =
      𝟙 _ := by
  subst h
  have h' :=
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p q).inv.naturality ψ
  dsimp only [Functor.comp_map, Functor.comp_obj] at h'
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp, ← h',
    ← Functor.map_comp_assoc, hT, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app]

/-- `eqToHom_comp_upperStarComp_hom_app_comp_map_comp_eq_id`, precomposed with a chain of four
morphisms (the shape in which it appears in `Correspondence.pointOpenRestriction`). -/
private lemma comp_comp_comp_comp_eqToHom_comp_upperStarComp_hom_app_comp_map {p : V ⟶ W}
    {q : W ⟶ Y} {j' : V ⟶ Y} (h : p ≫ q = j') {M N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {X₀ X₁ X₂ X₃ : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (c : X₂ ⟶ X₃) (d : X₃ ⟶ (boundedConstructibleUpperStar _ ℓ j').obj M)
    (T : (boundedConstructibleUpperStar _ ℓ q).obj M ⟶ (boundedConstructibleUpperStar _ ℓ q).obj N)
    (ψ : N ⟶ M) (hT : T ≫ (boundedConstructibleUpperStar _ ℓ q).map ψ = 𝟙 _) :
    a ≫ b ≫ c ≫ d ≫ eqToHom (by rw [h]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p q).hom.app M ≫
        (boundedConstructibleUpperStar _ ℓ p).map T ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p q).inv.app N ≫
        eqToHom (by rw [h]) ≫ (boundedConstructibleUpperStar _ ℓ j').map ψ =
      a ≫ b ≫ c ≫ d := by
  rw [eqToHom_comp_upperStarComp_hom_app_comp_map_comp_eq_id ℓ h T ψ hT, Category.comp_id]

end General

section OpenRestrict

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X W Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType W.hom]
  [QuasiCompact W.hom] [IsSeparated W.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]

/-- The restriction `Lj_W^* Rg^! ≅ Rg_W^! Lj^*` of the exceptional inverse image to open
subschemes is compatible with the triangle identity of `j_! ⊣ Lj^*`: the composite
```
Lj_W^* Rg^! K ≅ Rg_W^! Lj^* K --η--> Rg_W^! Lj^* j_! Lj^* K ≅ Lj_W^* Rg^! j_! Lj^* K
  --ε--> Lj_W^* Rg^! K
```
is the identity. -/
lemma boundedConstructibleUpperShriekOpenRestrict_hom_app_comp_map_unit_comp_inv_app_comp_map
    {jW : W ⟶ Y} {g : Y ⟶ X} {gW : W ⟶ U} {j : U ⟶ X} [IsOpenImmersion jW.left]
    [IsOpenImmersion j.left] (w : gW ≫ j = jW ≫ g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperShriekOpenRestrict ℓ w).hom.app K ≫
        (boundedConstructibleUpperShriek ℓ gW).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ j).unit.app _) ≫
        (boundedConstructibleUpperShriekOpenRestrict ℓ w).inv.app
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jW).map
        ((boundedConstructibleUpperShriek ℓ g).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ j).counit.app K)) =
      𝟙 ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jW).obj
        ((boundedConstructibleUpperShriek ℓ g).obj K)) :=
  Adjunction.iso_hom_app_comp_map_unit_comp_iso_inv_app_comp_map_map_counit _
    (boundedConstructibleUpperShriekOpenRestrict ℓ w) K

end OpenRestrict

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)
  (x : RationalPoint X)

-- Matching the unfolded `pointOpenRestriction` against the triangle identity requires unifying
-- several presentations of the same objects of `Dᵇc`, which is slow.
/-- **The open piece coefficient and the counit** (blueprint
`proposition-additivity-trace-classes--2`, proof of item 1, step (a)): `Rc₁^! ε ∘ u^U = u ∘ Lc₂^* ε`
for the counit `ε : j_! Lj^* K ⟶ K` of the open complement `j : X ∖ {x} ⟶ X` of a rational point,
when `c₂⁻¹(X ∖ {x}) ⊆ c₁⁻¹(X ∖ {x})`. -/
@[reassoc]
theorem pointOpenPieceCoeff_comp_map_counit
    (hle : c.c₂.left ⁻¹ᵁ pointComplOpens x ≤ c.c₁.left ⁻¹ᵁ pointComplOpens x) :
    c.pointOpenPieceCoeff x hle ≫
        (boundedConstructibleUpperShriek ℓ c.c₁).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
            (pointComplι x)).counit.app K) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
            (pointComplι x)).counit.app K) ≫ c.u := by
  rw [map_counit_comp_eq_openSquareExchange_hom_comp ℓ
      (isPullback_preimagePointComplRestrict c.c₂ x) K c.u _ rfl,
    pointOpenPieceCoeff, Category.assoc]
  congr 1
  rw [← Adjunction.homEquiv_naturality_right_symm]
  erw [← Adjunction.homEquiv_counit]
  refine congrArg _ ?_
  rw [pointOpenRestriction, boundedConstructiblePullbackSquareComparison_hom_app]
  simp only [Category.assoc]
  refine comp_comp_comp_comp_eqToHom_comp_upperStarComp_hom_app_comp_map ℓ
    (preimagePointComplHomOfLE_ι hle) _ _ _ _ _ _ ?_
  refine Eq.trans ?_
    (boundedConstructibleUpperShriekOpenRestrict_hom_app_comp_map_unit_comp_inv_app_comp_map ℓ
      (isPullback_preimagePointComplRestrict c.c₁ x).w K)
  congr 1

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
