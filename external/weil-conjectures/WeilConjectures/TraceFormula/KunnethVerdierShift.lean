/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.PoincareDuality.ProjectionFormulaShiftBoundedConstructible

/-!
# The Künneth–Verdier map is a morphism of triangulated functors

Fix `N ∈ Dᵇc(Y)⟦ℚ̄_ℓ⟧`. Both sides of the Künneth–Verdier map
```
κ_{M,N} : M ⊠ D_Y N ⟶ RHom(Lp_Y^* N, Rp_X^! M)
```
are triangulated functors of `M ∈ Dᵇc(X)⟦ℚ̄_ℓ⟧`, and `κ_{-,N}` is a natural transformation
compatible with the shifts (`ProEtale.CondensedRing.kunnethVerdierNatTrans`). Hence the objects `M`
for which `κ_{M,N}` is an isomorphism form a triangulated subcategory, closed under direct
summands: this is the two-out-of-three property on which the dévissage in `M` of the proof of the
Künneth–Verdier theorem rests (blueprint `proposition-exceptional-external-kunneth--1`,
`lemma-checking-isomorphisms-constructible-complexes--1`).

The compatibility with the shifts is obtained by writing `κ_{-,N}` as a composite of natural
transformations which commute with the shifts: `κ_{-,N}` is the transpose along
`Lp_Y^* N ⊗ᴸ - ⊣ RHom(Lp_Y^* N, -)` of the pairing
(`ProEtale.CondensedRing.kunnethVerdierPairingNatTrans`), a rearrangement of the tensor factors
followed by the exceptional Künneth map `α`
(`ProEtale.CondensedRing.exceptionalKunnethMapNatTrans`),
itself the transpose along `Rp_X! ⊣ Rp_X^!` of a composite of the braiding, the inverse of the
exceptional projection formula, compact-support base change, a counit and the left unitor
(`ProEtale.CondensedRing.exceptionalKunnethAdjointNatTrans_eq`).

## Main statements

- `ProEtale.CondensedRing.commShift_kunnethVerdierNatTrans`: `κ_{-,N}` commutes with the shifts.
- `ProEtale.CondensedRing.isIso_kunnethVerdierMap_of_triangEnvelope`: if `κ_{M,N}` is an
  isomorphism for `M` in a class `P`, it is one for `M` in the triangulated envelope of `P`.
- `ProEtale.CondensedRing.isIso_kunnethVerdierMap_of_distinguished`,
  `ProEtale.CondensedRing.isIso_kunnethVerdierMap_shift_iff`: two out of three and shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (X Y) in
/-- The adjoint `Rp_X! (M ⊠ ω_Y) ⟶ M` of the exceptional Künneth map, as a natural
transformation in `M`. -/
@[simps]
noncomputable def exceptionalKunnethAdjointNatTrans :
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X) ⋙
        (curriedTensor _).flip.obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (dualizingComplex' ℓ Y))) ⋙
      boundedConstructibleLowerShriek ℓ
        (prod.fst : X ⨯ Y ⟶ X) ⟶ 𝟭 _ where
  app M := exceptionalKunnethAdjoint ℓ (Y := Y) M
  naturality _ _ φ := by
    simp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app, Functor.id_map]
    exact exceptionalKunnethAdjoint_naturality ℓ (Y := Y) φ


variable (X Y) in
/-- The morphism `Rp_X! (Lp_Y^* ω_Y) ⟶ ℚ̄_ℓ` through which the adjoint of the exceptional Künneth
map factors: compact-support base change, the counit of `Ra_Y! ⊣ Ra_Y^!` and the unit
isomorphism of `La_X^*`. -/
noncomputable def exceptionalKunnethCounit :
    (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
          (dualizingComplex' ℓ Y)) ⟶ 𝟙_ _ :=
  (prodBaseChangeIso ℓ X Y).hom.app (dualizingComplex' ℓ Y) ≫
    (boundedConstructibleUpperStar _ ℓ (toPoint X)).map
      ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _)) ≫
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv

lemma exceptionalKunnethAdjointNatTrans_eq :
    exceptionalKunnethAdjointNatTrans ℓ X Y =
      Functor.whiskerRight (Functor.whiskerLeft
          (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X))
          (boundedConstructibleBraidingNatTrans₁
            ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
              (dualizingComplex' ℓ Y))))
          (boundedConstructibleLowerShriek ℓ (prod.fst : X ⨯ Y ⟶ X)) ≫
        inv (boundedConstructibleExceptionalProjectionOfCompactificationNatTrans ℓ
          (compactificationOverField (prod.fst : X ⨯ Y ⟶ X))
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (dualizingComplex' ℓ Y))) ≫
        (curriedTensor _).map (exceptionalKunnethCounit ℓ X Y) ≫
        leftUnitorNatTrans _ := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [exceptionalKunnethAdjointNatTrans_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, boundedConstructibleBraidingNatTrans₁_app, NatIso.isIso_inv_app,
    curriedTensor_map_app, leftUnitorNatTrans_app, exceptionalKunnethCounit,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  rfl


instance commShift_exceptionalKunnethAdjointNatTrans :
    NatTrans.CommShift (exceptionalKunnethAdjointNatTrans ℓ X Y) ℤ := by
  have := NatTrans.CommShift.of_isIso
    (boundedConstructibleExceptionalProjectionOfCompactificationNatTrans ℓ
      (compactificationOverField (prod.fst : X ⨯ Y ⟶ X))
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
        (dualizingComplex' ℓ Y))) ℤ
  rw [exceptionalKunnethAdjointNatTrans_eq]
  infer_instance


variable (X Y) in
/-- The exceptional Künneth map `α_{𝟙, a_Y} : M ⊠ ω_Y ⟶ Rp_X^! M`, as a natural transformation in
`M`. -/
@[simps]
noncomputable def exceptionalKunnethMapNatTrans :
    boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X) ⋙
        (curriedTensor _).flip.obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (dualizingComplex' ℓ Y)) ⟶
      𝟭 _ ⋙ boundedConstructibleUpperShriek ℓ
        (prod.fst : X ⨯ Y ⟶ X) where
  app M := exceptionalKunnethMap ℓ (Y := Y) M
  naturality _ _ φ := by
    simp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app, Functor.id_map]
    exact exceptionalKunnethMap_naturality ℓ (Y := Y) φ

instance commShift_exceptionalKunnethMapNatTrans :
    NatTrans.CommShift (exceptionalKunnethMapNatTrans ℓ X Y) ℤ :=
  NatTrans.CommShift.of_homEquiv
    (boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : X ⨯ Y ⟶ X))
    (exceptionalKunnethAdjointNatTrans ℓ X Y) _ (fun _ ↦ rfl)


variable (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

instance (A B : Dᵇc((X ⨯ Y).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (associatorNatTrans₂ (Dᵇc((X ⨯ Y).left)⟦Profinite.padicAlgClRingObj ℓ⟧) A B) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun Q ↦ inferInstanceAs (IsIso (α_ A Q B).hom)

/-- The morphism `Lp_Y^* N ⊗ Lp_Y^* D_Y N ⟶ Lp_Y^* ω_Y` of the Künneth–Verdier pairing: the
monoidal structure of `Lp_Y^*` followed by the evaluation `N ⊗ D_Y N ⟶ ω_Y`. -/
noncomputable def kunnethVerdierEvaluation :
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N ⊗
        (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
          (verdierDual ℓ N) ⟶
      (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj (dualizingComplex' ℓ Y) :=
  Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)) _ _ ≫
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map
      ((ihom.ev N).app (dualizingComplex' ℓ Y))

variable (X) in
/-- The Künneth–Verdier pairing `Lp_Y^* N ⊗ (M ⊠ D_Y N) ⟶ Rp_X^! M`, as a natural transformation
in `M`. -/
@[simps]
noncomputable def kunnethVerdierPairingNatTrans :
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X) ⋙
        (curriedTensor _).flip.obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (verdierDual ℓ N))) ⋙
      (curriedTensor _).obj ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N) ⟶
      𝟭 _ ⋙ boundedConstructibleUpperShriek ℓ
        (prod.fst : X ⨯ Y ⟶ X) where
  app M := kunnethVerdierPairing ℓ M N
  naturality _ _ φ := by
    simp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app,
      curriedTensor_obj_map, Functor.id_map]
    exact kunnethVerdierPairing_naturality ℓ (Y := Y) φ N

variable (X) in
/-- The rearrangement `Lp_Y^* N ⊗ (Q ⊗ Lp_Y^* D_Y N) ⟶ Q ⊗ Lp_Y^* ω_Y`, natural in `Q`, of the
Künneth–Verdier pairing: associators and the braiding of `Lp_Y^* N` past `Q`, followed by
`kunnethVerdierEvaluation`. -/
noncomputable def kunnethVerdierRearrangement :
    (curriedTensor _).flip.obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
          (verdierDual ℓ N)) ⋙
      (curriedTensor _).obj ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N) ⟶
      (curriedTensor _).flip.obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
          (dualizingComplex' ℓ Y)) :=
  inv (associatorNatTrans₂ _
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N)
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
        (verdierDual ℓ N))) ≫
    Functor.whiskerRight (boundedConstructibleBraidingNatTrans₂
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N))
      ((curriedTensor _).flip.obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
          (verdierDual ℓ N))) ≫
    associatorNatTrans₁ _ _ _ ≫
    (curriedTensor _).flip.map (kunnethVerdierEvaluation ℓ (X := X) N)

instance commShift_kunnethVerdierRearrangement :
    NatTrans.CommShift (kunnethVerdierRearrangement ℓ X N) ℤ := by
  have := NatTrans.CommShift.of_isIso (associatorNatTrans₂ _
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N)
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
      (verdierDual ℓ N))) ℤ
  dsimp only [kunnethVerdierRearrangement]
  infer_instance

/-- The Künneth–Verdier pairing is the rearrangement followed by the exceptional Künneth map. -/
lemma kunnethVerdierPairingNatTrans_eq :
    kunnethVerdierPairingNatTrans ℓ X N =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X))
          (kunnethVerdierRearrangement ℓ X N) ≫
        exceptionalKunnethMapNatTrans ℓ X Y := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [kunnethVerdierPairingNatTrans_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.isIso_inv_app,
    kunnethVerdierRearrangement, associatorNatTrans₂_app, associatorNatTrans₁_app,
    boundedConstructibleBraidingNatTrans₂_app, curriedTensor_map_app, Functor.flip_map_app,
    exceptionalKunnethMapNatTrans_app, kunnethVerdierEvaluation,
    MonoidalCategory.whiskerLeft_comp, Category.id_comp, Category.assoc, IsIso.Iso.inv_hom,
    Functor.flip_obj_map, curriedTensor_obj_map, kunnethVerdierPairing]

instance commShift_kunnethVerdierPairingNatTrans :
    NatTrans.CommShift (kunnethVerdierPairingNatTrans ℓ X N) ℤ := by
  rw [kunnethVerdierPairingNatTrans_eq]
  infer_instance

variable (X) in
/-- The Künneth–Verdier map `κ_{M,N}`, as a natural transformation in `M`. -/
@[simps]
noncomputable def kunnethVerdierNatTrans :
    boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X) ⋙
        (curriedTensor _).flip.obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (verdierDual ℓ N)) ⟶
      (𝟭 _ ⋙ boundedConstructibleUpperShriek ℓ
        (prod.fst : X ⨯ Y ⟶ X)) ⋙
        ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N) where
  app M := kunnethVerdierMap ℓ M N
  naturality _ _ φ := by
    simp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app, Functor.id_map]
    exact kunnethVerdierMap_naturality_left ℓ (Y := Y) φ N

instance commShift_kunnethVerdierNatTrans :
    NatTrans.CommShift (kunnethVerdierNatTrans ℓ X N) ℤ :=
  NatTrans.CommShift.of_homEquiv
    (boundedConstructibleTensorIhomAdjunction
      ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N))
    (kunnethVerdierPairingNatTrans ℓ X N) _ (fun _ ↦ rfl)

instance isTriangulated_isoLocus_kunnethVerdierNatTrans :
    (kunnethVerdierNatTrans ℓ X N).isoLocus.IsTriangulated := by
  have : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.fst : X ⨯ Y ⟶ X)).IsTriangulated := inferInstance
  have : (boundedConstructibleUpperShriek ℓ
      (prod.fst : X ⨯ Y ⟶ X)).IsTriangulated := inferInstance
  have : (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X) ⋙
        (curriedTensor _).flip.obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
            (verdierDual ℓ N))).IsTriangulated := inferInstance
  have : ((𝟭 _ ⋙ boundedConstructibleUpperShriek ℓ
        (prod.fst : X ⨯ Y ⟶ X)) ⋙
        ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N)).IsTriangulated :=
    inferInstance
  infer_instance

/-- **Dévissage for the Künneth–Verdier map** (the two-out-of-three property in the proof of
blueprint `proposition-exceptional-external-kunneth--1`): if `κ_{M,N}` is an isomorphism for the
objects `M` of a class `P`, it is an isomorphism for every `M` in the triangulated subcategory
generated by `P`. -/
lemma isIso_kunnethVerdierMap_of_triangEnvelope
    {P : ObjectProperty (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)}
    (h : ∀ M, P M → IsIso (kunnethVerdierMap ℓ M N))
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (hM : P.triangEnvelope M) :
    IsIso (kunnethVerdierMap ℓ M N) :=
  (P.triangEnvelope_le_iff (Q := (kunnethVerdierNatTrans ℓ X N).isoLocus)).2 h M hM

/-- **Two out of three for the Künneth–Verdier map**: for a distinguished triangle
`M₁ ⟶ M₂ ⟶ M₃ ⟶ M₁[1]` of `Dᵇc(X)⟦ℚ̄_ℓ⟧`, if `κ_{M₁,N}` and `κ_{M₃,N}` are isomorphisms, so is
`κ_{M₂,N}`. -/
lemma isIso_kunnethVerdierMap_of_distinguished
    (T : Pretriangulated.Triangle (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    (hT : T ∈ Pretriangulated.distinguishedTriangles) [IsIso (kunnethVerdierMap ℓ T.obj₁ N)]
    [IsIso (kunnethVerdierMap ℓ T.obj₃ N)] : IsIso (kunnethVerdierMap ℓ T.obj₂ N) :=
  ObjectProperty.ext_of_isTriangulatedClosed₂ (kunnethVerdierNatTrans ℓ X N).isoLocus T hT
    (inferInstanceAs (IsIso (kunnethVerdierMap ℓ T.obj₁ N)))
    (inferInstanceAs (IsIso (kunnethVerdierMap ℓ T.obj₃ N)))

/-- The Künneth–Verdier map `κ_{M[n],N}` is an isomorphism if and only if `κ_{M,N}` is. -/
lemma isIso_kunnethVerdierMap_shift_iff (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (n : ℤ) :
    IsIso (kunnethVerdierMap ℓ (M⟦n⟧) N) ↔ IsIso (kunnethVerdierMap ℓ M N) :=
  NatTrans.isIso_app_shift_iff (kunnethVerdierNatTrans ℓ X N) M n

end AlgebraicGeometry.ProEtale.CondensedRing
