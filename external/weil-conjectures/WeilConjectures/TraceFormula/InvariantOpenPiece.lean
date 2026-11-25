/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingOpenPiece
public import WeilConjectures.TraceFormula.Specialization.PointsSupport

/-!

# The open piece of a correspondence along an invariant open subscheme

Let `c = (c₁, c₂) : C ⟶ X × X` be an endocorrespondence of `(X, K)` with coefficient map
`u : Lc₂^* K ⟶ Rc₁^! K`, and let `U ⊆ X` be an open subscheme with
`c₂⁻¹(U) ⊆ c₁⁻¹(U)`, i.e. its closed complement `Z` satisfies `c₁⁻¹(Z) ⊆ c₂⁻¹(Z)`
(blueprint `lemma-lift-correspondence-invariant-decomposition`). Then `u` induces a coefficient
map on the open piece `K_U = j_! Lj^* K`:

* `u_U = [j]_! (u|_U) : Lc₂^* K_U ⟶ Rc₁^! K_U`
  (`ProEtale.CondensedRing.Correspondence.openPieceCoeff`): the open base change
  `Lc₂^* j_! ≅ j_{V!} Lc_{2,V}^*` followed by the `j_{V!} ⊣ Lj_V^*` adjoint of the restriction
  of `u` to the open correspondence `V = c₂⁻¹(U) ⟶ U × U`;
* it is compatible with the counit `ε : K_U ⟶ K`, `Rc₁^! ε ∘ u_U = u ∘ Lc₂^* ε`
  (`ProEtale.CondensedRing.Correspondence.openPieceCoeff_comp_map_counit`).

This generalizes `Correspondence.pointOpenPieceCoeff` and
`Correspondence.pointOpenPieceCoeff_comp_map_counit` from the complement of a rational point to an
arbitrary open subscheme, with the same proof.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Preimages of open subschemes -/

section Preimage

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))}

/-- The restriction `g⁻¹(U) ⟶ U` of `g : Y ⟶ X` to the preimage of an open subscheme `U`. -/
noncomputable def opensOverRestrict (g : Y ⟶ X) (U : X.left.Opens) :
    opensOver (g.left ⁻¹ᵁ U) ⟶ opensOver U :=
  Over.homMk (g.left ∣_ U) (by
    change _ ≫ U.ι ≫ X.hom = _
    rw [morphismRestrict_ι_assoc, Over.w g]
    rfl)

/-- The restriction of `g` to the preimage of an open subscheme is a base change of `g`. -/
lemma isPullback_opensOverRestrict (g : Y ⟶ X) (U : X.left.Opens) :
    IsPullback (opensOverRestrict g U) (opensOverι (g.left ⁻¹ᵁ U)) (opensOverι U) g := by
  have w : opensOverRestrict g U ≫ opensOverι U = opensOverι (g.left ⁻¹ᵁ U) ≫ g := by
    ext1
    exact morphismRestrict_ι _ _
  exact IsPullback.of_map (Over.forget _) w (isPullback_morphismRestrict g.left U)

/-- The inclusion `V ⟶ W` of open subschemes `V ≤ W`, as a morphism over `s`. -/
noncomputable def opensOverHomOfLE {V W : Y.left.Opens} (hle : V ≤ W) :
    opensOver V ⟶ opensOver W :=
  Over.homMk (Y.left.homOfLE hle) (by
    change _ ≫ W.ι ≫ Y.hom = _
    rw [Scheme.homOfLE_ι_assoc]
    rfl)

@[reassoc (attr := simp)]
lemma opensOverHomOfLE_ι {V W : Y.left.Opens} (hle : V ≤ W) :
    opensOverHomOfLE hle ≫ opensOverι W = opensOverι V := by
  ext1
  exact Scheme.homOfLE_ι _ hle

instance {V W : Y.left.Opens} (hle : V ≤ W) : IsOpenImmersion (opensOverHomOfLE hle).left :=
  inferInstanceAs (IsOpenImmersion (Y.left.homOfLE hle))

end Preimage

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {V W Y : Over (Spec (.of k))}
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom] [LocallyOfFiniteType W.hom]
  [QuasiCompact W.hom] [IsSeparated W.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- `eqToHom_comp_upperStarComp_hom_app_comp_map_comp_eq_id`, precomposed with a chain of four
morphisms (the shape in which it appears in `openRestrictionOfIsPullback`). -/
private lemma comp_comp_comp_comp_eqToHom_comp_upperStarComp_hom_app_comp_map' {p : V ⟶ W}
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

/-! ### The open piece coefficient of a pair of cartesian squares -/

section Squares

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X C U V W : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  {c₁ c₂ : C ⟶ X} {j : U ⟶ X} {jV : V ⟶ C} {jW : W ⟶ C} {gV : V ⟶ U} {gW : W ⟶ U} {ι : V ⟶ W}
  [IsOpenImmersion j.left] [IsOpenImmersion jV.left] [IsOpenImmersion jW.left]
  (sqV : IsPullback gV jV j c₂) (sqW : IsPullback gW jW j c₁) (hι : ι ≫ jW = jV)
  (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
    (boundedConstructibleUpperShriek ℓ c₁).obj K)

/-- The restriction
```
Lg_V^* Lj^* K ≅ Lj_V^* Lc₂^* K --u--> Lj_V^* Rc₁^! K ≅ Lι^* Lj_W^* Rc₁^! K
  ≅ Lι^* Rg_W^! Lj^* K ⟶ Lι^* Rg_W^! Lj^* j_! Lj^* K ≅ Lι^* Lj_W^* Rc₁^! j_! Lj^* K
  ≅ Lj_V^* Rc₁^! j_! Lj^* K
```
of a coefficient map `u : Lc₂^* K ⟶ Rc₁^! K` along cartesian squares `g_V ≫ j = j_V ≫ c₂`,
`g_W ≫ j = j_W ≫ c₁` of open immersions with `ι ≫ j_W = j_V`, followed by the unit of
`j_! ⊣ Lj^*`. -/
noncomputable def openRestrictionOfIsPullback :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ gV).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jV).obj
        ((boundedConstructibleUpperShriek ℓ c₁).obj
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
            j).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))) :=
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ gV j).inv.app K ≫
    eqToHom (by rw [sqV.w]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ jV c₂).hom.app K ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jV).map u ≫
    eqToHom (by rw [hι]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ι jW).hom.app _ ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ι).map
      ((boundedConstructibleUpperShriekOpenRestrict ℓ sqW.w).hom.app K ≫
        (boundedConstructibleUpperShriek ℓ gW).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ j).unit.app _) ≫
        (boundedConstructibleUpperShriekOpenRestrict ℓ sqW.w).inv.app
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ι jW).inv.app
      ((boundedConstructibleUpperShriek ℓ c₁).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))) ≫
    eqToHom (by rw [hι])

/-- The *open piece coefficient* `[j]_! (u|_U) : Lc₂^* j_! Lj^* K ⟶ Rc₁^! j_! Lj^* K` of a
coefficient map along cartesian squares of open immersions: the open base change
`Lc₂^* j_! ≅ j_{V!} Lg_V^*` followed by the `j_{V!} ⊣ Lj_V^*` adjoint of
`openRestrictionOfIsPullback`. -/
noncomputable def openPieceCoeffOfIsPullback :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) ⟶
      (boundedConstructibleUpperShriek ℓ c₁).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K)) :=
  (openSquareExchange ℓ sqV).hom.app _ ≫
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ jV).homEquiv _ _).symm
      (openRestrictionOfIsPullback ℓ sqV sqW hι K u)

-- Matching the unfolded restriction against the triangle identity requires unifying several
-- presentations of the same objects of `Dᵇc`, which is slow.
/-- **The open piece coefficient and the counit**: `Rc₁^! ε ∘ [j]_! (u|_U) = u ∘ Lc₂^* ε` for the
counit `ε : j_! Lj^* K ⟶ K`. -/
theorem openPieceCoeffOfIsPullback_comp_map_counit :
    openPieceCoeffOfIsPullback ℓ sqV sqW hι K u ≫
        (boundedConstructibleUpperShriek ℓ c₁).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K) ≫
        u := by
  rw [map_counit_comp_eq_openSquareExchange_hom_comp ℓ sqV K u _ rfl,
    openPieceCoeffOfIsPullback, Category.assoc]
  congr 1
  rw [← Adjunction.homEquiv_naturality_right_symm]
  erw [← Adjunction.homEquiv_counit]
  refine congrArg _ ?_
  rw [openRestrictionOfIsPullback, boundedConstructiblePullbackSquareComparison_hom_app]
  simp only [Category.assoc]
  refine comp_comp_comp_comp_eqToHom_comp_upperStarComp_hom_app_comp_map' ℓ hι _ _ _ _ _ _ ?_
  refine Eq.trans ?_
    (boundedConstructibleUpperShriekOpenRestrict_hom_app_comp_map_unit_comp_inv_app_comp_map ℓ
      sqW.w K)
  congr 1

end Squares

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The *open piece* `K_U = j_! Lj^* K` of `K` along an open subscheme `j : U ⟶ X`. -/
noncomputable abbrev openPiece (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (U : X.left.Opens) : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (opensOverι U)).obj
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (opensOverι U)).obj K)

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)
  (U : X.left.Opens)

/-- The *open piece coefficient* `u_U = [j]_! (u|_U) : Lc₂^* K_U ⟶ Rc₁^! K_U` of a
correspondence along an open subscheme `j : U ⟶ X` with `c₂⁻¹(U) ⊆ c₁⁻¹(U)` (blueprint
`lemma-lift-correspondence-invariant-decomposition`): the open base change
`Lc₂^* j_! ≅ j_{V!} Lc_{2,V}^*` followed by the `j_{V!} ⊣ Lj_V^*` adjoint of the restriction of
`u` to the open correspondence `V = c₂⁻¹(U) ⟶ U × U` (`openPieceCoeffOfIsPullback`). -/
noncomputable def openPieceCoeff (hle : c.c₂.left ⁻¹ᵁ U ≤ c.c₁.left ⁻¹ᵁ U) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
        (openPiece K U) ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj (openPiece K U) :=
  openPieceCoeffOfIsPullback ℓ (isPullback_opensOverRestrict c.c₂ U)
    (isPullback_opensOverRestrict c.c₁ U) (opensOverHomOfLE_ι hle) K c.u

/-- **The open piece coefficient and the counit** (blueprint
`lemma-lift-correspondence-invariant-decomposition`, the open piece): `Rc₁^! ε ∘ u_U = u ∘ Lc₂^* ε`
for the counit `ε : j_! Lj^* K ⟶ K` of an open subscheme `j : U ⟶ X` with
`c₂⁻¹(U) ⊆ c₁⁻¹(U)`. -/
theorem openPieceCoeff_comp_map_counit (hle : c.c₂.left ⁻¹ᵁ U ≤ c.c₁.left ⁻¹ᵁ U) :
    c.openPieceCoeff U hle ≫
        (boundedConstructibleUpperShriek ℓ c.c₁).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
            (opensOverι U)).counit.app K) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
            (opensOverι U)).counit.app K) ≫ c.u :=
  openPieceCoeffOfIsPullback_comp_map_counit ℓ _ _ _ K c.u

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
