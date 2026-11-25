/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom

/-!
# Internal homs of Weil complexes

Let `Λ` be a finite coefficient ring and `g` an automorphism of a scheme `X` of finite type over a
field on which the exponent of `Λ` is invertible. The *internal-Hom Frobenius* of two Weil
complexes `(K, φ_K)` and `(L, φ_L)` is the composite
`Lg^* RHom(K, L) ≅ RHom(Lg^* K, Lg^* L) ⟶ RHom(K, L)`, the second arrow being
`RHom(φ_K⁻¹, φ_L)` (`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius`). The first arrow
is the comparison map of the monoidal functor `Lg^*`, an isomorphism because `Lg^*` is an
equivalence, `g` being an automorphism.

With this Frobenius the derived internal hom becomes a bifunctor
`RHom(-, -) : WeilDᵒᵖ × WeilD ⥤ WeilD` (`AlgebraicGeometry.Etale.WeilComplex.internalHom`)
lying over the derived internal hom of `Dctf(X, Λ)`, which is triangulated in its second
variable. See `WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom` for the model of the
Weil category used here.

## Main definitions

- `AlgebraicGeometry.Etale.WeilComplex.derivedHomFrobenius`: the internal-Hom Frobenius in
  `D(X_ét)`, for any coefficient category.
- `AlgebraicGeometry.Etale.WeilComplex.liftBifunctor`: a bifunctor
  `Dctf(X, A)ᵒᵖ × Dctf(X, A) ⥤ Dctf(X, A)` with Weil structures on its values, natural in both
  variables, lifts to Weil complexes.
- `AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius` (`prose-10-20`).
- `AlgebraicGeometry.Etale.WeilComplex.internalHom` (`prose-10-20`).

## Implementation notes

The constructions are made for an arbitrary coefficient category `A` and only then specialised
to `A = ModuleCat Λ`; this is for the kernel. Lean replaces the proofs nested in the body of a
definition by auxiliary theorems (`abstractNestedProofs`), but only the non-atomic ones. At
`ModuleCat Λ` the instance `HasSmallSiteSheafify (ModuleCat Λ)` is the non-atomic proof
`HasSmallSiteSheafify.of_isGrothendieckAbelian (ModuleCat Λ)`, and it occurs in every
`WeilComplex (ModuleCat Λ) g`, so a definition written directly at `ModuleCat Λ` stores a copy of
its morphisms that differs from the statements of its lemmas in that proof. The kernel then
cannot compare the two morphisms argument by argument (they are applications of projections such
as `NatTrans.app`) and evaluates the derived internal hom instead, for minutes per declaration.
Over a general `A` the proof is the atomic `HasSmallSiteSheafify.of_isGrothendieckAbelian A`, so
nothing is abstracted, and the specialisation to `ModuleCat Λ` produces exactly the terms of the
statements. For the same reason the generic declarations do not take `[HasSmallSiteSheafify A]`
as a hypothesis but let it be found from `[IsGrothendieckAbelian A]`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

namespace WeilComplex

section Coefficients

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [UpperStarPreservesFlat A] {X : Scheme.{u}} {g : X ≅ X}

/-- The compatibility of a morphism of Weil complexes with the inverses of the Weil
structures. -/
lemma frobenius_inv_comp_map {K L : WeilComplex A g} (f : K ⟶ L) :
    K.frobenius.inv ≫ (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).map f.hom =
      f.hom ≫ L.frobenius.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, f.comm, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The *internal-Hom Frobenius* of two Weil complexes `(K, φ_K)` and `(L, φ_L)` in `D(X_ét)`:
the composite `Lg^* RHom(K, L) ⟶ RHom(Lg^* K, Lg^* L) ⟶ RHom(K, L)` of the comparison map of
the monoidal functor `Lg^*` and of `RHom(φ_K⁻¹, φ_L)`, an isomorphism since `g` is one. -/
noncomputable def derivedHomFrobenius (K L : WeilComplex A g) :
    L((g.hom)^*[A]).obj ((RHom(X)[A].obj (op K.obj.obj)).obj L.obj.obj) ≅
      (RHom(X)[A].obj (op K.obj.obj)).obj L.obj.obj :=
  asIso (leftDerivedUpperStarDerivedHomComparison A g.hom K.obj.obj L.obj.obj ≫
    (RHom(X)[A].map K.frobenius.inv.hom.op).app _ ≫
      (RHom(X)[A].obj (op K.obj.obj)).map L.frobenius.hom.hom)

lemma derivedHomFrobenius_hom (K L : WeilComplex A g) :
    (derivedHomFrobenius K L).hom =
      leftDerivedUpperStarDerivedHomComparison A g.hom K.obj.obj L.obj.obj ≫
        (RHom(X)[A].map K.frobenius.inv.hom.op).app _ ≫
          (RHom(X)[A].obj (op K.obj.obj)).map L.frobenius.hom.hom :=
  rfl

/-- The internal-Hom Frobenius in `D(X_ét)` is natural in the first variable: an instance of
`AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedHomComparison_comp_naturality_left`. -/
lemma derivedHomFrobenius_hom_naturality_left {K K' : WeilComplex A g} (f : K' ⟶ K)
    (L : WeilComplex A g) :
    (derivedHomFrobenius K L).hom ≫ (RHom(X)[A].map f.hom.hom.op).app L.obj.obj =
      L((g.hom)^*[A]).map ((RHom(X)[A].map f.hom.hom.op).app L.obj.obj) ≫
        (derivedHomFrobenius K' L).hom := by
  rw [derivedHomFrobenius_hom, derivedHomFrobenius_hom]
  exact leftDerivedUpperStarDerivedHomComparison_comp_naturality_left _ g.hom f.hom.hom _ _ _
    (congrArg InducedCategory.Hom.hom (frobenius_inv_comp_map f))

/-- `AlgebraicGeometry.Etale.WeilComplex.derivedHomFrobenius_hom_naturality_left` with `f`
written as `f.hom.op.unop.hom`, the form in which it appears after rewriting with
`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.derivedHom_map_app_hom`. Stating it in this form
lets the kernel check its use at `ModuleCat Λ` syntactically. -/
lemma derivedHomFrobenius_hom_naturality_left_unop {K K' : WeilComplex A g} (f : K' ⟶ K)
    (L : WeilComplex A g) :
    (derivedHomFrobenius K L).hom ≫ (RHom(X)[A].map f.hom.op.unop.hom.op).app L.obj.obj =
      L((g.hom)^*[A]).map ((RHom(X)[A].map f.hom.op.unop.hom.op).app L.obj.obj) ≫
        (derivedHomFrobenius K' L).hom :=
  derivedHomFrobenius_hom_naturality_left f L

section Lift

variable (H : (DerivedCategoryFiniteTor A X)ᵒᵖ ⥤ DerivedCategoryFiniteTor A X ⥤
    DerivedCategoryFiniteTor A X)
  (φ : ∀ K L : WeilComplex A g, (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).obj
    ((H.obj (op K.obj)).obj L.obj) ≅ (H.obj (op K.obj)).obj L.obj)
  (hφ : ∀ (K : WeilComplex A g) {L L' : WeilComplex A g} (h : L ⟶ L'),
    (φ K L).hom ≫ (H.obj (op K.obj)).map h.hom =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).map
          ((H.obj (op K.obj)).map h.hom) ≫ (φ K L').hom)
  (hφ' : ∀ {K K' : WeilComplex A g} (f : K' ⟶ K) (L : WeilComplex A g),
    (φ K L).hom ≫ (H.map f.hom.op).app L.obj =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar A g.hom).map ((H.map f.hom.op).app L.obj) ≫
        (φ K' L).hom)

/-- The functor `H(K, -)` on Weil complexes, for a bifunctor `H` on `Dctf(X, A)` together with
Weil structures `φ K L` on its values which are natural in `L`. -/
noncomputable def liftBifunctorObj (K : WeilComplex A g) :
    WeilComplex A g ⥤ WeilComplex A g where
  obj L := ⟨(H.obj (op K.obj)).obj L.obj, φ K L⟩
  map h := ⟨(H.obj (op K.obj)).map h.hom, hφ K h⟩
  map_id L := Hom.ext ((H.obj (op K.obj)).map_id L.obj)
  map_comp h h' := Hom.ext ((H.obj (op K.obj)).map_comp h.hom h'.hom)

/-- The component at `L` of the natural transformation `H(K, -) ⟶ H(K', -)` of functors on Weil
complexes induced by a morphism `f : K' ⟶ K`, when the Weil structures `φ K L` are also natural
in `K`. -/
noncomputable def liftBifunctorMapApp {K K' : WeilComplex A g} (f : K' ⟶ K)
    (L : WeilComplex A g) :
    (liftBifunctorObj H φ hφ K).obj L ⟶ (liftBifunctorObj H φ hφ K').obj L :=
  ⟨(H.map f.hom.op).app L.obj, hφ' f L⟩

lemma liftBifunctorMapApp_naturality {K K' : WeilComplex A g} (f : K' ⟶ K)
    {L L' : WeilComplex A g} (h : L ⟶ L') :
    (liftBifunctorObj H φ hφ K).map h ≫ liftBifunctorMapApp H φ hφ hφ' f L' =
      liftBifunctorMapApp H φ hφ hφ' f L ≫ (liftBifunctorObj H φ hφ K').map h :=
  Hom.ext ((H.map f.hom.op).naturality h.hom)

/-- The natural transformation `H(K, -) ⟶ H(K', -)` of functors on Weil complexes induced by a
morphism `f : K' ⟶ K`. -/
noncomputable def liftBifunctorMap {K K' : WeilComplex A g} (f : K' ⟶ K) :
    liftBifunctorObj H φ hφ K ⟶ liftBifunctorObj H φ hφ K' where
  app := liftBifunctorMapApp H φ hφ hφ' f
  naturality _ _ := liftBifunctorMapApp_naturality H φ hφ hφ' f

lemma liftBifunctorMap_id (K : WeilComplex A g) :
    liftBifunctorMap H φ hφ hφ' (𝟙 K) = 𝟙 (liftBifunctorObj H φ hφ K) :=
  NatTrans.ext <| funext fun L ↦ Hom.ext (NatTrans.congr_app (H.map_id (op K.obj)) L.obj)

lemma liftBifunctorMap_comp {K K' K'' : WeilComplex A g} (f : K' ⟶ K) (f' : K'' ⟶ K') :
    liftBifunctorMap H φ hφ hφ' (f' ≫ f) =
      liftBifunctorMap H φ hφ hφ' f ≫ liftBifunctorMap H φ hφ hφ' f' :=
  NatTrans.ext <| funext fun L ↦ Hom.ext (NatTrans.congr_app (H.map_comp f.hom.op f'.hom.op) L.obj)

/-- A bifunctor `H : Dctf(X, A)ᵒᵖ ⥤ Dctf(X, A) ⥤ Dctf(X, A)` together with Weil structures
`φ K L` on its values, natural in both variables, lifts to a bifunctor on Weil complexes. -/
noncomputable def liftBifunctor :
    (WeilComplex A g)ᵒᵖ ⥤ WeilComplex A g ⥤ WeilComplex A g where
  obj K := liftBifunctorObj H φ hφ K.unop
  map f := liftBifunctorMap H φ hφ hφ' f.unop
  map_id K := liftBifunctorMap_id H φ hφ hφ' K.unop
  map_comp f f' := liftBifunctorMap_comp H φ hφ hφ' f.unop f'.unop

end Lift

end Coefficients

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}} {g : X ≅ X}

omit [Finite Λ] in
/-- The compatibility of a morphism of Weil complexes with the inverses of the Weil structures,
in `D(X_ét)`. -/
@[reassoc]
lemma frobenius_inv_hom_comp_map {K L : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K ⟶ L) :
    K.frobenius.inv.hom ≫ L((g.hom)^*[ModuleCat.{u + 1} Λ]).map f.hom.hom =
      f.hom.hom ≫ L.frobenius.inv.hom := by
  rw [← cancel_mono ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).hom]
  rw [Category.assoc, Category.assoc]
  change _ = _ ≫ ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).inv ≫
    ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).hom
  rw [Iso.inv_hom_id, Category.comp_id]
  change _ ≫ _ ≫ L.frobenius.hom.hom = _
  rw [← frobenius_hom_comp_hom]
  change ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius).inv ≫
    ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

variable {k : Type u} [Field k] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasInvertibleExponent Λ X]

/-- Blueprint `prose-10-20`: the *internal-Hom Frobenius* of two Weil complexes
`(K, φ_K)` and `(L, φ_L)`, the Weil structure
`Lg^* RHom(K, L) ≅ RHom(Lg^* K, Lg^* L) ≅ RHom(K, L)` on `RHom(K, L)`, whose first arrow is the
comparison map of the monoidal equivalence `Lg^*` and whose second arrow is
`RHom(φ_K⁻¹, φ_L)` (`AlgebraicGeometry.Etale.WeilComplex.derivedHomFrobenius`). -/
noncomputable def internalHomFrobenius (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).obj
        (((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).obj L.obj) ≅
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).obj L.obj :=
  ObjectProperty.isoMk _ (derivedHomFrobenius K L)

lemma internalHomFrobenius_hom_hom (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomFrobenius aX K L).hom.hom =
      leftDerivedUpperStarDerivedHomComparison (ModuleCat.{u + 1} Λ) g.hom K.obj.obj L.obj.obj ≫
        (RHom(X)[ModuleCat.{u + 1} Λ].map K.frobenius.inv.hom.op).app _ ≫
          (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map L.frobenius.hom.hom :=
  rfl

/-- The internal-Hom Frobenius is natural in the second variable. -/
lemma internalHomFrobenius_hom_comp_map_right (K : WeilComplex (ModuleCat.{u + 1} Λ) g)
    {L L' : WeilComplex (ModuleCat.{u + 1} Λ) g} (h : L ⟶ L') :
    (internalHomFrobenius aX K L).hom ≫
        ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).map h.hom =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).map
          (((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).map h.hom) ≫
        (internalHomFrobenius aX K L').hom := by
  apply ObjectProperty.hom_ext
  change (internalHomFrobenius aX K L).hom.hom ≫
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map h.hom.hom =
    L((g.hom)^*[ModuleCat.{u + 1} Λ]).map
        ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map h.hom.hom) ≫
      (internalHomFrobenius aX K L').hom.hom
  rw [internalHomFrobenius_hom_hom, internalHomFrobenius_hom_hom,
    leftDerivedUpperStarDerivedHomComparison_naturality_right_assoc, Category.assoc,
    Category.assoc, NatTrans.naturality_assoc, ← Functor.map_comp, ← Functor.map_comp,
    frobenius_hom_comp_hom]

omit [Finite Λ] [HasInvertibleExponent Λ X] in
/-- The naturality of the internal-Hom Frobenius in the first variable, in `D(X_ét)`: an instance
of `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedHomComparison_comp_naturality_left`. -/
lemma internalHomFrobenius_aux {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g}
    (f : K' ⟶ K) (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (leftDerivedUpperStarDerivedHomComparison (ModuleCat.{u + 1} Λ) g.hom K.obj.obj L.obj.obj ≫
      (RHom(X)[ModuleCat.{u + 1} Λ].map K.frobenius.inv.hom.op).app _ ≫
        (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map L.frobenius.hom.hom) ≫
      (RHom(X)[ModuleCat.{u + 1} Λ].map f.hom.hom.op).app L.obj.obj =
    L((g.hom)^*[ModuleCat.{u + 1} Λ]).map ((RHom(X)[ModuleCat.{u + 1} Λ].map f.hom.hom.op).app
        L.obj.obj) ≫
      leftDerivedUpperStarDerivedHomComparison (ModuleCat.{u + 1} Λ) g.hom K'.obj.obj L.obj.obj ≫
        (RHom(X)[ModuleCat.{u + 1} Λ].map K'.frobenius.inv.hom.op).app _ ≫
          (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K'.obj.obj)).map L.frobenius.hom.hom :=
  derivedHomFrobenius_hom_naturality_left f L

/-- The internal-Hom Frobenius is natural in the first variable. -/
lemma internalHomFrobenius_hom_comp_map_left {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g}
    (f : K' ⟶ K) (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomFrobenius aX K L).hom ≫
        ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).map
          (((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj) ≫
        (internalHomFrobenius aX K' L).hom := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    DerivedCategoryFiniteTor.leftDerivedUpperStar_map_hom,
    DerivedCategoryFiniteTor.derivedHom_map_app_hom]
  exact derivedHomFrobenius_hom_naturality_left_unop f L

/-- The derived internal hom `RHom(K, -)` of a Weil complex `K`, as an endofunctor of Weil
complexes: the Weil structure of `RHom(K, L)` is the internal-Hom Frobenius
(`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius`). -/
noncomputable def internalHomObj (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    WeilComplex (ModuleCat.{u + 1} Λ) g ⥤ WeilComplex (ModuleCat.{u + 1} Λ) g :=
  liftBifunctorObj (DerivedCategoryFiniteTor.derivedHom Λ aX) (internalHomFrobenius aX)
    (internalHomFrobenius_hom_comp_map_right aX) K

/-- The component at `L` of the natural transformation `RHom(K, -) ⟶ RHom(K', -)` induced by a
morphism `f : K' ⟶ K` of Weil complexes. -/
noncomputable def internalHomMapApp {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomObj aX K).obj L ⟶ (internalHomObj aX K').obj L :=
  liftBifunctorMapApp (DerivedCategoryFiniteTor.derivedHom Λ aX) (internalHomFrobenius aX)
    (internalHomFrobenius_hom_comp_map_right aX) (internalHomFrobenius_hom_comp_map_left aX) f L

/-- The components `internalHomMapApp` are natural in the second variable. -/
lemma internalHomMap_naturality {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    {L L' : WeilComplex (ModuleCat.{u + 1} Λ) g} (h : L ⟶ L') :
    (internalHomObj aX K).map h ≫ internalHomMapApp aX f L' =
      internalHomMapApp aX f L ≫ (internalHomObj aX K').map h :=
  liftBifunctorMapApp_naturality _ _ _ _ f h

/-- The natural transformation `RHom(K, -) ⟶ RHom(K', -)` of endofunctors of Weil complexes
induced by a morphism `f : K' ⟶ K` of Weil complexes. -/
noncomputable def internalHomMap {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K) :
    internalHomObj aX K ⟶ internalHomObj aX K' :=
  liftBifunctorMap (DerivedCategoryFiniteTor.derivedHom Λ aX) (internalHomFrobenius aX)
    (internalHomFrobenius_hom_comp_map_right aX) (internalHomFrobenius_hom_comp_map_left aX) f

@[simp]
lemma internalHomMapApp_hom {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomMapApp aX f L).hom =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj :=
  rfl

@[simp]
lemma internalHomMap_app {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomMap aX f).app L = internalHomMapApp aX f L :=
  rfl

lemma internalHomMap_id (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    internalHomMap aX (𝟙 K) = 𝟙 (internalHomObj aX K) :=
  liftBifunctorMap_id _ _ _ _ K

lemma internalHomMap_comp {K K' K'' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (f' : K'' ⟶ K') :
    internalHomMap aX (f' ≫ f) = internalHomMap aX f ≫ internalHomMap aX f' :=
  liftBifunctorMap_comp _ _ _ _ f f'

variable (g) in
/-- Blueprint `prose-10-20`: the derived internal hom of Weil complexes. With the
internal-Hom Frobenius `RHom(φ_K⁻¹, φ_L)`
(`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius`), the derived internal hom of
`Dctf(X, Λ)` lifts to a bifunctor `WeilDᵒᵖ × WeilD ⥤ WeilD` on Weil complexes, lying over the
derived internal hom of `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.WeilComplex.internalHom_obj_obj_obj`,
`…internalHom_map_app_hom`, `…internalHom_obj_map_hom`), which is triangulated in its second
variable. -/
noncomputable def internalHom :
    (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ ⥤ WeilComplex (ModuleCat.{u + 1} Λ) g ⥤
      WeilComplex (ModuleCat.{u + 1} Λ) g :=
  liftBifunctor (DerivedCategoryFiniteTor.derivedHom Λ aX) (internalHomFrobenius aX)
    (internalHomFrobenius_hom_comp_map_right aX) (internalHomFrobenius_hom_comp_map_left aX)

@[simp]
lemma internalHom_obj_obj_obj (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).obj K).obj L).obj =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).obj L.obj :=
  rfl

@[simp]
lemma internalHom_obj_obj_frobenius (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).obj K).obj L).frobenius = internalHomFrobenius aX K.unop L :=
  rfl

@[simp]
lemma internalHom_obj_map_hom (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    {L L' : WeilComplex (ModuleCat.{u + 1} Λ) g} (h : L ⟶ L') :
    (((internalHom g aX).obj K).map h).hom =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).map h.hom :=
  rfl

@[simp]
lemma internalHom_map_app_hom {K K' : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ} (f : K ⟶ K')
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).map f).app L).hom =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.unop.hom.op).app L.obj :=
  rfl

end WeilComplex

end Etale

end AlgebraicGeometry
