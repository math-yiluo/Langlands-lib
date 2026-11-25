/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.FiberMapCongr
public import WeilConjectures.WeilSheaf.CondensedModelWeilDerived
public import WeilConjectures.WeilSheaf.CondensedModelDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraMapDerivedComp

/-!
# Base change of the condensed lower shriek to the geometric fibres

Let `k` be a finite field, `f : X₀ ⟶ Y₀` a morphism of `k`-schemes with a compactification
`c = (X₀ ⟶[i] Z₀ ⟶[g] Y₀)`, and `p : X̄ ⟶ X₀` the projections of the geometric fibres. The
projections are weakly étale (`AlgebraicGeometry.Scheme.Hom.weaklyEtale_geometricFiberProj`), so
the pullbacks `p^*` of module objects over a commutative condensed ring `Λ` commute with the
direct image with compact support: this is the "easy" (localization) case of base change, which
needs no properness.

## Module objects

- `AlgebraicGeometry.ProEtale.CondensedRing.lowerStarBaseChangeIso` and
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerStarBaseChangeIso`: for a cartesian
  square with weakly étale horizontal maps, `g^* ∘ f_* ≅ f'_* ∘ g'^*`, also on the derived
  categories (`Rf_* ⋙ D(g^*) ≅ D(g'^*) ⋙ Rf'_*`).
- `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriekUpperStarBaseChangeIso`: for a
  cartesian square of open immersions along weakly étale maps, `j_! ⋙ f^* ≅ f'^* ⋙ j'_!`, the
  conjugate of the weakly étale base change of the pushforward along the composite adjunctions.
- `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactificationBaseChangeIso`:
  `Rf_!(c) ⋙ D(p_Y^*) ≅ D(p_X^*) ⋙ Rf'_!(c')` for compactifications `c`, `c'` related by cartesian
  squares with weakly étale vertical maps.
- `AlgebraicGeometry.Compactification.geometricFiber`: the base change `c̄` of a compactification
  to the geometric fibres, and
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekGeometricFiberIso`:
  `Rf_!(c) ⋙ D(p_Y^*) ≅ D(p_X^*) ⋙ Rf̄_!(c̄)`.

## Weil objects

The canonical Weil structure `(Fr⁻¹)_* p^* M ≅ p^* M` of a pulled-back object
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilLowerStar`) is compared with the Weil
structures of `geometricFiberMapWeilUpperStar`, `geometricFiberMapWeilLowerStar` and
`weilExtensionByZero`, which are defined as
(iterated) mates of the Frobenius exchange of the pushforward. The whole comparison is reduced to
a single Frobenius compatibility, for the pullback comparison `φ^* ⋙ p_X^* ≅ p_Y^* ⋙ φ̄^*`
(`AlgebraicGeometry.ProEtale.CondensedRing.UpperStarWeilCompatible`): given it,

- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarCompGeometricFiberWeilLowerStarIso` lifts the
  pullback comparison to Weil objects;
- its mate along `φ^* ⊣ φ_*` and the lifted adjunction `geometricFiberMapWeilUpperStar ⊣
  geometricFiberMapWeilLowerStar` is the
  base change morphism `geometricFiberWeil (φ_* M) ⟶ geometricFiberMapWeilLowerStar φ
  (geometricFiberWeil M)`
  (`AlgebraicGeometry.ProEtale.CondensedRing.lowerStarGeometricFiberWeilBaseChange`), an
  isomorphism since its underlying morphism is the weakly étale base change morphism;
- its inverse mate along `j_! ⊣ j^*` and `weilExtensionByZero ⊣ geometricFiberMapWeilUpperStar` is
the base change
  morphism of extension by zero
  (`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilExtensionByZeroBaseChange`), an
  isomorphism since its conjugate along the composite adjunctions is a weakly étale base change
  morphism (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`);
- `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilRightDerivedLowerShriekIso`:
  the condensed Weil `Rf̄_!`
  (`AlgebraicGeometry.ProEtale.CondensedRing.weilRightDerivedLowerShriek`, which is
  `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRightDerivedLowerShriek` for `Λ = ℚ̲̄_ℓ`)
  of `geometricFiberWeil M` is `geometricFiberWeil (Rf_! M)`:
  `D(geometricFiberWeil) ⋙ Rf̄_! ≅ Rf_!(c) ⋙ D(geometricFiberWeil)`.

The derived statement uses
`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso`:
`R(T ⋙ mapOfNatIso e) ≅ D(T) ⋙ R(mapOfNatIso e)` for an exact functor `T` to algebras whose
underlying functor preserves K-injective complexes (here `p^*`, right adjoint to the exact
extension by zero along the weakly étale `p`).

## Implementation notes

The underlying morphisms of the Weil-level mates are computed in the abstract setting of
`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_mateEquiv_mapOfNatIsoAdjunction`), with the
identifications `geometricFiberWeilLowerStar ⋙ forget = p^*` passed as equations of functors, so
that the kernel does not unfold the pullback functors.
-/

@[expose] public section

universe w₀ w w' v v' u u'

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section WeaklyEtaleBaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Weakly étale base change for the pushforward of module objects**, as an isomorphism. -/
noncomputable def lowerStarBaseChangeIso (hsq : IsPullback g' f' f g) [WeaklyEtale g]
    [WeaklyEtale g'] : (f)_*⟦Λ⟧ ⋙ (g)^*⟦Λ⟧ ≅ (g')^*⟦Λ⟧ ⋙ (f')_*⟦Λ⟧ :=
  have := isIso_lowerStarBaseChange_of_isPullback Λ hsq
  asIso (lowerStarBaseChange Λ hsq.toCommSq)

/-- **Extension by zero commutes with weakly étale pullback**: for a cartesian square
`g' ≫ f = f' ≫ g` with open immersions `g`, `g'` and weakly étale `f`, `f'`,
`g_! ⋙ f^* ≅ f'^* ⋙ g'_!`. It is the conjugate, along the composite adjunctions
`g_! ⋙ f^* ⊣ f_* ⋙ g^*` and `f'^* ⋙ g'_! ⊣ g'^* ⋙ f'_*`, of the weakly étale base change
`f_* ⋙ g^* ≅ g'^* ⋙ f'_*` along the open immersion `g`. -/
noncomputable def openImmersionLowerShriekUpperStarBaseChangeIso (hsq : IsPullback g' f' f g)
    [IsOpenImmersion g] [IsOpenImmersion g'] :
    (g)_!open⟦Λ⟧ ⋙ (f)^*⟦Λ⟧ ≅ (f')^*⟦Λ⟧ ⋙ (g')_!open⟦Λ⟧ :=
  ((conjugateIsoEquiv ((openImmersionLowerShriekUpperStarAdjunction Λ g).comp
      (upperStarLowerStarAdjunction Λ f))
    ((upperStarLowerStarAdjunction Λ f').comp
      (openImmersionLowerShriekUpperStarAdjunction Λ g'))).symm
    (lowerStarBaseChangeIso Λ hsq)).symm

/-- **Derived weakly étale base change**: for a cartesian square `g' ≫ f = f' ≫ g` with `g` and
`g'` weakly étale, `Rf_* ⋙ D(g^*) ≅ D(g'^*) ⋙ Rf'_*`, from
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale` and the
identification of the derived pullbacks with the levelwise ones. -/
noncomputable def rightDerivedLowerStarBaseChangeIso (hsq : IsPullback g' f' f g) [WeaklyEtale g]
    [WeaklyEtale g'] :
    ((f)_*⟦Λ⟧).rightDerivedFunctor ⋙ D((g)^*⟦Λ⟧) ≅
      D((g')^*⟦Λ⟧) ⋙ ((f')_*⟦Λ⟧).rightDerivedFunctor :=
  have := isIso_baseChangeMap_of_weaklyEtale Λ hsq
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm ≪≫
    asIso (baseChangeMap Λ hsq.toCommSq) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g') _

/-- Derived extension by zero commutes with weakly étale pullback:
`D(g_!) ⋙ D(f^*) ≅ D(f'^*) ⋙ D(g'_!)`, all functors being exact. -/
noncomputable def openImmersionLowerShriekMapDerivedCategoryBaseChangeIso
    (hsq : IsPullback g' f' f g) [IsOpenImmersion g] [IsOpenImmersion g'] :
    D((g)_!open⟦Λ⟧) ⋙ D((f)^*⟦Λ⟧) ≅ D((f')^*⟦Λ⟧) ⋙ D((g')_!open⟦Λ⟧) :=
  Functor.mapDerivedCategoryCompIsoOfIso (openImmersionLowerShriekUpperStarBaseChangeIso Λ hsq)

end WeaklyEtaleBaseChange

section LowerShriek

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **Weakly étale base change for the direct image with compact support**: for compactifications
`c = (X ⟶[i] Z ⟶[g] Y)` of `f` and `c' = (X' ⟶[i'] Z' ⟶[g'] Y')` of `f'`, related by
cartesian squares
```
X' --i'--> Z' --g'--> Y'
|pX         |pZ         |pY
v           v           v
X ---i---> Z ---g----> Y
```
with `pZ` and `pY` weakly étale, `Rf_!(c) ⋙ D(pY^*) ≅ D(pX^*) ⋙ Rf'_!(c')`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChangeIso
    (c : Compactification f) (c' : Compactification f') {pX : X' ⟶ X} {pZ : c'.Z ⟶ c.Z}
    {pY : Y' ⟶ Y} (hi : IsPullback c'.i pX pZ c.i) (hg : IsPullback pZ c'.g c.g pY)
    [WeaklyEtale pZ] [WeaklyEtale pY] :
    Rf_!(c)⟦Λ⟧ ⋙ D((pY)^*⟦Λ⟧) ≅ D((pX)^*⟦Λ⟧) ⋙ Rf_!(c')⟦Λ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarBaseChangeIso Λ hg) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ hi) _ ≪≫
    Functor.associator _ _ _

end LowerShriek

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X₀ Y₀ : Scheme.{u}} {s : X₀ ⟶ Spec (.of k)}
  {t : Y₀ ⟶ Spec (.of k)}

namespace Compactification

variable {f : X₀ ⟶ Y₀}

/-- The structure morphism `s` of `X₀` is `i ≫ g ≫ t` for a compactification `X₀ ⟶[i] Z₀ ⟶[g] Y₀`
of a morphism `f` with `f ≫ t = s`. -/
lemma i_comp_g_comp (c : Compactification f) (h : f ≫ t = s) : c.i ≫ c.g ≫ t = s := by
  rw [← Category.assoc, ← c.comm, h]

/-- The base change `c̄ = (X̄ ⟶[ī] Z̄ ⟶[ḡ] Ȳ)` to the geometric fibres of a compactification
`c = (X₀ ⟶[i] Z₀ ⟶[g] Y₀)` of a morphism `f` of `k`-schemes: a compactification of the base change
`f̄`, open immersions and proper morphisms being stable under base change. Here `Z₀` is a
`k`-scheme through `g ≫ t`. -/
@[simps]
noncomputable def geometricFiber (c : Compactification f) (h : f ≫ t = s) :
    Compactification (Scheme.Hom.geometricFiberMap f h) where
  Z := (c.g ≫ t).geometricFiber
  g := Scheme.Hom.geometricFiberMap c.g rfl
  i := Scheme.Hom.geometricFiberMap c.i (c.i_comp_g_comp h)
  comm := by
    rw [← Scheme.Hom.geometricFiberMap_comp]
    exact Scheme.Hom.geometricFiberMap_congr c.comm _ _
  isProper := Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) _ _
    c.isProper
  isOpenImmersion := inferInstance

end Compactification

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {s : X₀ ⟶ Spec (.of k)}
  {t : Y₀ ⟶ Spec (.of k)} {f : X₀ ⟶ Y₀}

/-- **The direct image with compact support commutes with the pullback to the geometric fibres**:
for a compactification `c` of a morphism `f : X₀ ⟶ Y₀` of `k`-schemes and its base change `c̄`
to the geometric fibres, `Rf_!(c) ⋙ D(p_Y^*) ≅ D(p_X^*) ⋙ Rf̄_!(c̄)`. -/
noncomputable def rightDerivedLowerShriekGeometricFiberIso (c : Compactification f)
    (h : f ≫ t = s) :
    Rf_!(c)⟦Λ⟧ ⋙ D((t.geometricFiberProj)^*⟦Λ⟧) ≅
      D((s.geometricFiberProj)^*⟦Λ⟧) ⋙ Rf_!(c.geometricFiber h)⟦Λ⟧ :=
  rightDerivedLowerShriekOfCompactificationBaseChangeIso Λ c (c.geometricFiber h)
    (Scheme.Hom.isPullback_geometricFiberMap c.i (c.i_comp_g_comp h))
    (Scheme.Hom.isPullback_geometricFiberMap c.g rfl).flip

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### Right derived functors of transports precomposed with exact functors to algebras -/

namespace CategoryTheory.Endofunctor.IsoAlgebra

open Limits

variable {A : Type*} [Category A] [Abelian A]
  {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w} (IsoAlgebra F)]
  [HasDerivedCategory.{w'} (IsoAlgebra G)] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]
  (T : A ⥤ IsoAlgebra F) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  {T₀ : A ⥤ C} [T₀.Additive] [T₀.PreservesKInjectiveComplexes]

omit [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w} (IsoAlgebra F)]
  [HasDerivedCategory.{w} C] [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions A]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C] in
/-- If the underlying functor `T₀` of a functor `T` to algebras preserves K-injective complexes,
the underlying complex of `T K` is K-injective for every K-injective complex `K`. -/
lemma isKInjective_forget_map_map_of_iso (α : T ⋙ forget F ≅ T₀)
    (K : CochainComplex A ℤ) [K.IsKInjective] :
    CochainComplex.IsKInjective (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  CochainComplex.isKInjective_of_iso
    ((Functor.mapHomologicalComplexCompIso α (ComplexShape.up ℤ)).app K).symm

/-- If `T : A ⥤ IsoAlgebra F` is exact and its underlying functor preserves K-injective complexes,
then `D(T) ⋙ R(mapOfNatIso e)` is a right derived functor of `T ⋙ mapOfNatIso e`. -/
lemma isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_mapOfNatIso_of_iso
    (α : T ⋙ forget F ≅ T₀) :
    (T.mapDerivedCategory ⋙ (mapOfNatIso e).rightDerivedFunctor).IsRightDerivedFunctor
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((T ⋙ mapOfNatIso e).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  have := isKInjective_forget_map_map_of_iso T α K
  have h₂ := isIso_rightDerivedFunctorUnit_app_mapOfNatIso e
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have h₂' : IsIso ((mapOfNatIso e).rightDerivedFunctorUnit.app
      ((T.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.KInjectives.localizerMorphism A).functor.obj
          (HomotopyCategory.KInjectives.mk K)))) := h₂
  have h₃ : IsIso ((mapOfNatIso e).rightDerivedFunctor.map (T.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.KInjectives.localizerMorphism A).functor.obj
        (HomotopyCategory.KInjectives.mk K)))) :=
    inferInstanceAs (IsIso ((mapOfNatIso e).rightDerivedFunctor.mapIso
      (T.mapDerivedCategoryFactorsh.app _).symm).hom)
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  infer_instance

/-- **Right derived functors of transports precomposed with exact functors to algebras**:
`R(T ⋙ mapOfNatIso e) ≅ D(T) ⋙ R(mapOfNatIso e)` for an exact `T : A ⥤ IsoAlgebra F` whose
underlying functor preserves K-injective complexes. -/
noncomputable def rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso (α : T ⋙ forget F ≅ T₀) :
    (T ⋙ mapOfNatIso e).rightDerivedFunctor ≅
      T.mapDerivedCategory ⋙ (mapOfNatIso e).rightDerivedFunctor :=
  have := isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_mapOfNatIso_of_iso
    e T α
  Functor.rightDerivedUnique _ _ (T ⋙ mapOfNatIso e).rightDerivedFunctorUnit
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

section Lift

variable {B : Type*} [Category B] {B' : Type*} [Category B']
  {C : Type u} [Category.{v} C] {F : C ⥤ C} {D : Type u'} [Category.{v'} D] {G : D ⥤ D}

/-- An isomorphism between the underlying functors of two functors to algebras which commutes
with the structure isomorphisms is an isomorphism of functors to algebras. -/
@[simps!]
noncomputable def isoMkOfForget {P Q : B ⥤ IsoAlgebra F} (e : P ⋙ forget F ≅ Q ⋙ forget F)
    (he : ∀ b, F.map (e.hom.app b) ≫ (Q.obj b).str.hom = (P.obj b).str.hom ≫ e.hom.app b) :
    P ≅ Q :=
  NatIso.ofComponents (fun b ↦ ObjectProperty.isoMk _ (Algebra.isoMk (e.app b) (by
      rw [← str_hom, ← str_hom]
      exact he b)))
    (fun f ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext (e.hom.naturality f)))

/-- The underlying natural transformation of the inverse of `isoMkOfForget e he` is `e.inv`. -/
@[simp]
lemma whiskerRight_isoMkOfForget_inv_forget {P Q : B ⥤ IsoAlgebra F}
    (e : P ⋙ forget F ≅ Q ⋙ forget F)
    (he : ∀ b, F.map (e.hom.app b) ≫ (Q.obj b).str.hom = (P.obj b).str.hom ≫ e.hom.app b) :
    Functor.whiskerRight (isoMkOfForget e he).inv (forget F) = e.inv :=
  rfl

/-- The underlying natural transformation of `isoMkOfForget e he` is `e.hom`. -/
@[simp]
lemma whiskerRight_isoMkOfForget_hom_forget {P Q : B ⥤ IsoAlgebra F}
    (e : P ⋙ forget F ≅ Q ⋙ forget F)
    (he : ∀ b, F.map (e.hom.app b) ≫ (Q.obj b).str.hom = (P.obj b).str.hom ≫ e.hom.app b) :
    Functor.whiskerRight (isoMkOfForget e he).hom (forget F) = e.hom :=
  rfl

variable {l : B ⥤ B'} {r : B' ⥤ B} (adjB : l ⊣ r) {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
  (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)) = eR.hom)
  {PB : B ⥤ IsoAlgebra F} {PB' : B' ⥤ IsoAlgebra G}

/-- The mate along a lifted adjunction of algebras is computed on underlying objects. -/
lemma mateEquiv_mapOfNatIsoAdjunction_app_hom_f
    (α : TwoSquare PB l (mapOfNatIso eL) PB') (b' : B') :
    ((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR h) α).app b').hom.f =
      (mateEquiv adjB adj (TwoSquare.mk (PB ⋙ forget F) l L (PB' ⋙ forget G)
        (Functor.whiskerRight α (forget G)))).app b' := by
  simp [mateEquiv_apply, mapOfNatIsoAdjunction]

/-- The inverse mate along a lifted adjunction of algebras is computed on underlying objects. -/
lemma mateEquiv_symm_mapOfNatIsoAdjunction_app_hom_f
    (β : TwoSquare r PB' PB (mapOfNatIso eR)) (b : B) :
    (((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR h)).symm β).app b).hom.f =
      ((mateEquiv adjB adj).symm (TwoSquare.mk r (PB' ⋙ forget G) (PB ⋙ forget F) R
        (Functor.whiskerRight β (forget F)))).app b := by
  simp [mateEquiv_symm_apply, mapOfNatIsoAdjunction]


/-- **Isomorphism criterion for mates of algebras.** Let `θ : PB ⋙ L ≅ l ⋙ PB'` be an
isomorphism of functors to algebras whose underlying isomorphism is `θ₀ : P₀ ⋙ L ≅ l ⋙ P₀'`.
If the mate of `θ₀⁻¹` along `l ⊣ r` and `L ⊣ R` is an isomorphism, so is the mate of `θ⁻¹` along
`l ⊣ r` and the lifted adjunction. -/
lemma isIso_mateEquiv_mapOfNatIsoAdjunction {P₀ : B ⥤ C} {P₀' : B' ⥤ D}
    (hP : PB ⋙ forget F = P₀) (hP' : PB' ⋙ forget G = P₀')
    (θ : l ⋙ PB' ≅ PB ⋙ mapOfNatIso eL) (θ₀ : l ⋙ P₀' ≅ P₀ ⋙ L)
    (hθ : ∀ b, (θ.inv.app b).hom.f = eqToHom (by rw [← hP]; rfl) ≫ θ₀.inv.app b ≫
      eqToHom (by rw [← hP']; rfl))
    [IsIso (mateEquiv adjB adj (TwoSquare.mk _ _ _ _ θ₀.inv))] :
    IsIso (mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR h)
      (TwoSquare.mk _ _ _ _ θ.inv)) := by
  subst hP hP'
  have hθ' : Functor.whiskerRight θ.inv (forget G) = θ₀.inv := by
    ext b
    simpa using hθ b
  have (b' : B') : IsIso ((forget F).map
      ((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR h)
        (TwoSquare.mk _ _ _ _ θ.inv)).app b')) := by
    have e := mateEquiv_mapOfNatIsoAdjunction_app_hom_f adjB adj eL eR h
      (TwoSquare.mk _ _ _ _ θ.inv) b'
    rw [hθ'] at e
    rw [forget_map, e]
    infer_instance
  have (b' : B') : IsIso ((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR h)
      (TwoSquare.mk _ _ _ _ θ.inv)).app b') :=
    isIso_of_reflects_iso _ (forget F)
  exact NatIso.isIso_of_isIso_app _

/-- **Isomorphism criterion for inverse mates of algebras**: the analogue of
`CategoryTheory.Endofunctor.IsoAlgebra.isIso_mateEquiv_mapOfNatIsoAdjunction` for
`(mateEquiv _ _).symm`. -/
lemma isIso_mateEquiv_symm_mapOfNatIsoAdjunction {P₀ : B ⥤ C} {P₀' : B' ⥤ D}
    (hP : PB ⋙ forget F = P₀) (hP' : PB' ⋙ forget G = P₀')
    (θ : r ⋙ PB ≅ PB' ⋙ mapOfNatIso eR) (θ₀ : r ⋙ P₀ ≅ P₀' ⋙ R)
    (hθ : ∀ b', (θ.hom.app b').hom.f = eqToHom (by rw [← hP]; rfl) ≫ θ₀.hom.app b' ≫
      eqToHom (by rw [← hP']; rfl))
    [IsIso ((mateEquiv adjB adj).symm (TwoSquare.mk _ _ _ _ θ₀.hom))] :
    IsIso ((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR h)).symm
      (TwoSquare.mk _ _ _ _ θ.hom)) := by
  subst hP hP'
  have hθ' : Functor.whiskerRight θ.hom (forget F) = θ₀.hom := by
    ext b
    simpa using hθ b
  have (b : B) : IsIso ((forget G).map
      (((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR h)).symm
        (TwoSquare.mk _ _ _ _ θ.hom)).app b)) := by
    have e := mateEquiv_symm_mapOfNatIsoAdjunction_app_hom_f adjB adj eL eR h
      (TwoSquare.mk _ _ _ _ θ.hom) b
    rw [hθ'] at e
    rw [forget_map, e]
    infer_instance
  have (b : B) : IsIso (((mateEquiv adjB (mapOfNatIsoAdjunction adj eL eR h)).symm
      (TwoSquare.mk _ _ _ _ θ.hom)).app b) :=
    isIso_of_reflects_iso _ (forget G)
  exact NatIso.isIso_of_isIso_app _

end Lift

end CategoryTheory.Endofunctor.IsoAlgebra
/-! ### Pullback to the geometric fibres and the Weil functors -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {s : X₀ ⟶ Spec (.of k)}
  {t : Y₀ ⟶ Spec (.of k)}

variable (s) in
/-- The pulled-back Weil objects `p^* M` are left exact in `M`, since `p^*` is and the forgetful
functor reflects finite limits. -/
instance preservesFiniteLimits_geometricFiberWeilLowerStar :
    PreservesFiniteLimits (geometricFiberWeilLowerStar Λ s) := by
  have : PreservesFiniteLimits (geometricFiberWeilLowerStar Λ s ⋙
      Endofunctor.IsoAlgebra.forget _) :=
    inferInstanceAs (PreservesFiniteLimits (s.geometricFiberProj)^*⟦Λ⟧)
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Endofunctor.IsoAlgebra.forget _)

variable (s) in
/-- The pulled-back Weil objects `p^* M` are right exact in `M`. -/
instance preservesFiniteColimits_geometricFiberWeilLowerStar :
    PreservesFiniteColimits (geometricFiberWeilLowerStar Λ s) := by
  have : PreservesFiniteColimits (geometricFiberWeilLowerStar Λ s ⋙
      Endofunctor.IsoAlgebra.forget _) :=
    inferInstanceAs (PreservesFiniteColimits (s.geometricFiberProj)^*⟦Λ⟧)
  exact preservesFiniteColimits_of_reflects_of_preserves _ (Endofunctor.IsoAlgebra.forget _)

variable (s) in
instance : (geometricFiberWeilLowerStar Λ s).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (s) in
/-- The underlying object of `geometricFiberWeilLowerStar M` is `p^* M`. -/
@[simp]
lemma geometricFiberWeilLowerStar_obj_carrier
    (M : Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)) :
    ((geometricFiberWeilLowerStar Λ s).obj M).carrier = (s.geometricFiberProj)^*⟦Λ⟧.obj M :=
  rfl

variable (s) in
/-- The structure isomorphism of `geometricFiberWeilLowerStar M` is the canonical one. -/
@[simp]
lemma geometricFiberWeilLowerStar_obj_str_hom
    (M : Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)) :
    ((geometricFiberWeilLowerStar Λ s).obj M).str.hom =
      (geometricFiberProjLowerStarFrobeniusIso Λ s).hom.app M :=
  rfl

/-- The pullback along a weakly étale morphism preserves K-injective complexes, being right
adjoint to the exact extension by zero. -/
instance preservesKInjectiveComplexes_upperStar_of_weaklyEtale {X Y : Scheme.{u}} (g : X ⟶ Y)
    [WeaklyEtale g] : (g)^*⟦Λ⟧.PreservesKInjectiveComplexes :=
  (weaklyEtaleLowerShriekUpperStarAdjunction Λ g).preservesKInjectiveComplexes

section Exchange

variable (φ : X₀ ⟶ Y₀) (h : φ ≫ t = s)

/-- The comparison `φ^* ⋙ p_X^* ≅ p_Y^* ⋙ φ̄^*` of the pullbacks around the base change square of
`φ` to the geometric fibres. -/
noncomputable def geometricFiberUpperStarComparison :
    (φ)^*⟦Λ⟧ ⋙ (s.geometricFiberProj)^*⟦Λ⟧ ≅
      (t.geometricFiberProj)^*⟦Λ⟧ ⋙ (Scheme.Hom.geometricFiberMap φ h)^*⟦Λ⟧ :=
  (upperStarSquareComparison Λ (Scheme.Hom.isPullback_geometricFiberMap φ h).flip.toCommSq).symm

/-- **Frobenius compatibility of the pullback comparison**: the comparison
`p_X^* φ^* N ≅ φ̄^* p_Y^* N` intertwines the canonical Weil structure of `p_X^* (φ^* N)`
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilLowerStar`) with the Weil structure
of `geometricFiberMapWeilUpperStar φ (p_Y^* N)`. -/
def UpperStarWeilCompatible : Prop :=
  ∀ N, (lowerStar Λ s.geometricGaloisFrobenius.asIso.inv).map
      ((geometricFiberUpperStarComparison Λ φ h).hom.app N) ≫
      ((geometricFiberMapWeilUpperStar Λ φ h).obj
        ((geometricFiberWeilLowerStar Λ t).obj N)).str.hom =
    ((geometricFiberWeilLowerStar Λ s).obj ((φ)^*⟦Λ⟧.obj N)).str.hom ≫
      (geometricFiberUpperStarComparison Λ φ h).hom.app N

variable {Λ φ h}

/-- The pullback comparison as an isomorphism of Weil objects, given its Frobenius
compatibility: `geometricFiberWeil (φ^* N) ≅ geometricFiberMapWeilUpperStar φ (geometricFiberWeil
N)`. -/
noncomputable def upperStarCompGeometricFiberWeilLowerStarIso
    (hc : UpperStarWeilCompatible Λ φ h) :
    (φ)^*⟦Λ⟧ ⋙ geometricFiberWeilLowerStar Λ s ≅
      geometricFiberWeilLowerStar Λ t ⋙ geometricFiberMapWeilUpperStar Λ φ h :=
  Endofunctor.IsoAlgebra.isoMkOfForget (geometricFiberUpperStarComparison Λ φ h) hc

/-- The base change morphism `geometricFiberWeil (φ_* M) ⟶ geometricFiberMapWeilLowerStar φ
(geometricFiberWeil M)`
of Weil objects, the mate of the pullback comparison. -/
noncomputable def lowerStarGeometricFiberWeilBaseChange (hc : UpperStarWeilCompatible Λ φ h) :
    (φ)_*⟦Λ⟧ ⋙ geometricFiberWeilLowerStar Λ t ⟶
      geometricFiberWeilLowerStar Λ s ⋙ geometricFiberMapWeilLowerStar Λ φ h :=
  (mateEquiv (upperStarLowerStarAdjunction Λ φ)
    (Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction
      (upperStarLowerStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))
      (upperStarGeometricFiberMapCompFrobeniusIso Λ φ h)
      (lowerStarGeometricFiberMapCompFrobeniusIso Λ φ h)
      (Endofunctor.IsoAlgebra.mateEquiv_leftMateIso_inv _ _))
    (TwoSquare.mk (geometricFiberWeilLowerStar Λ t) (φ)^*⟦Λ⟧
      (Endofunctor.IsoAlgebra.mapOfNatIso (upperStarGeometricFiberMapCompFrobeniusIso Λ φ h))
      (geometricFiberWeilLowerStar Λ s)
      (upperStarCompGeometricFiberWeilLowerStarIso hc).inv))

/-- Weakly étale base change for the pushforward of Weil objects: the base change morphism
`geometricFiberWeil (φ_* M) ⟶ geometricFiberMapWeilLowerStar φ (geometricFiberWeil M)` is an
isomorphism, its
underlying morphism being the weakly étale base change morphism of module objects. -/
instance isIso_lowerStarGeometricFiberWeilBaseChange (hc : UpperStarWeilCompatible Λ φ h) :
    IsIso (lowerStarGeometricFiberWeilBaseChange hc) := by
  have : IsIso (mateEquiv (upperStarLowerStarAdjunction Λ φ)
      (upperStarLowerStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))
      (TwoSquare.mk _ _ _ _ (geometricFiberUpperStarComparison Λ φ h).inv)) := by
    rw [geometricFiberUpperStarComparison, Iso.symm_inv, ← Adjunction.exchangeRight_eq_mateEquiv,
      ← lowerStarBaseChange_eq]
    exact isIso_lowerStarBaseChange_of_isPullback Λ
      (Scheme.Hom.isPullback_geometricFiberMap φ h).flip
  exact Endofunctor.IsoAlgebra.isIso_mateEquiv_mapOfNatIsoAdjunction _ _ _ _ _
    (P₀ := (t.geometricFiberProj)^*⟦Λ⟧) (P₀' := (s.geometricFiberProj)^*⟦Λ⟧) rfl rfl
    (upperStarCompGeometricFiberWeilLowerStarIso hc) (geometricFiberUpperStarComparison Λ φ h)
    (fun N ↦ by simp [upperStarCompGeometricFiberWeilLowerStarIso])


/-- The comparison of the pullbacks around the flipped square is the inverse comparison. -/
lemma upperStarSquareComparison_flip_inv {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    (upperStarSquareComparison Λ sq.flip).inv = (upperStarSquareComparison Λ sq).hom := by
  rw [upperStarSquareComparison, upperStarSquareComparison]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, eqToIso.inv, eqToIso.hom,
    Category.assoc]

section OpenImmersion

variable [IsOpenImmersion φ]

/-- The base change morphism `weilExtensionByZero φ (geometricFiberWeil M) ⟶
geometricFiberWeil (φ_! M)` of Weil objects along an open immersion `φ`, the inverse mate of the
pullback comparison. -/
noncomputable def geometricFiberWeilExtensionByZeroBaseChange
    (hc : UpperStarWeilCompatible Λ φ h) :
    geometricFiberWeilLowerStar Λ s ⋙ weilExtensionByZero Λ φ h ⟶
      (φ)_!open⟦Λ⟧ ⋙ geometricFiberWeilLowerStar Λ t :=
  ((mateEquiv (openImmersionLowerShriekUpperStarAdjunction Λ φ)
    (Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction
      (openImmersionLowerShriekUpperStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))
      (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ φ h)
      (upperStarGeometricFiberMapCompFrobeniusIso Λ φ h)
      (Endofunctor.IsoAlgebra.mateEquiv_leftMateIso_inv _ _))).symm
    (TwoSquare.mk (φ)^*⟦Λ⟧ (geometricFiberWeilLowerStar Λ t) (geometricFiberWeilLowerStar Λ s)
      (Endofunctor.IsoAlgebra.mapOfNatIso (upperStarGeometricFiberMapCompFrobeniusIso Λ φ h))
      (upperStarCompGeometricFiberWeilLowerStarIso hc).hom))

/-- Extension by zero commutes with the pullback to the geometric fibres on Weil objects: the
base change morphism is an isomorphism. Its underlying morphism is the inverse mate of the
pullback comparison along the extensions by zero, whose conjugate along the composite
adjunctions is the weakly étale base change morphism `φ^* p_{Y*} ⟶ p_{X*} φ̄^*`. -/
instance isIso_geometricFiberWeilExtensionByZeroBaseChange (hc : UpperStarWeilCompatible Λ φ h) :
    IsIso (geometricFiberWeilExtensionByZeroBaseChange hc) := by
  let α := ((mateEquiv (openImmersionLowerShriekUpperStarAdjunction Λ φ)
    (openImmersionLowerShriekUpperStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))).symm
    (TwoSquare.mk _ _ _ _ (geometricFiberUpperStarComparison Λ φ h).hom))
  have hc' := iterated_mateEquiv_conjugateEquiv
    (openImmersionLowerShriekUpperStarAdjunction Λ φ)
    (openImmersionLowerShriekUpperStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))
    (upperStarLowerStarAdjunction Λ s.geometricFiberProj)
    (upperStarLowerStarAdjunction Λ t.geometricFiberProj) α
  have : IsIso (conjugateEquiv ((openImmersionLowerShriekUpperStarAdjunction Λ φ).comp
      (upperStarLowerStarAdjunction Λ t.geometricFiberProj))
      ((upperStarLowerStarAdjunction Λ s.geometricFiberProj).comp
        (openImmersionLowerShriekUpperStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h)))
      α) := by
    rw [← hc', Equiv.apply_symm_apply, geometricFiberUpperStarComparison, Iso.symm_hom,
      upperStarSquareComparison_flip_inv (Λ := Λ)
        (Scheme.Hom.isPullback_geometricFiberMap φ h).toCommSq]
    have hb := isIso_lowerStarBaseChange_of_isPullback Λ
      (Scheme.Hom.isPullback_geometricFiberMap φ h)
    rw [lowerStarBaseChange_eq, Adjunction.exchangeRight_eq_mateEquiv] at hb
    exact hb
  have : IsIso α := conjugateEquiv_of_iso
    ((openImmersionLowerShriekUpperStarAdjunction Λ φ).comp
      (upperStarLowerStarAdjunction Λ t.geometricFiberProj))
    ((upperStarLowerStarAdjunction Λ s.geometricFiberProj).comp
      (openImmersionLowerShriekUpperStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))) _
  exact Endofunctor.IsoAlgebra.isIso_mateEquiv_symm_mapOfNatIsoAdjunction _ _ _ _ _
    (P₀ := (s.geometricFiberProj)^*⟦Λ⟧) (P₀' := (t.geometricFiberProj)^*⟦Λ⟧) rfl rfl
    (upperStarCompGeometricFiberWeilLowerStarIso hc) (geometricFiberUpperStarComparison Λ φ h)
    (fun N ↦ by simp [upperStarCompGeometricFiberWeilLowerStarIso])

end OpenImmersion
end Exchange

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### The direct image with compact support of pulled-back Weil objects -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {s : X₀ ⟶ Spec (.of k)}
  {t : Y₀ ⟶ Spec (.of k)}

section Derived

variable {Λ}

/-- Derived pushforward of Weil objects and pullback to the geometric fibres:
`D(p_X^*) ⋙ R(geometricFiberMapWeilLowerStar φ) ≅ R(φ_*) ⋙ D(p_Y^*)`, given the Frobenius
compatibility of the
pullback comparison of `φ`. -/
noncomputable def geometricFiberWeilRightDerivedLowerStarIso
    {φ : X₀ ⟶ Y₀} {h : φ ≫ t = s} (hc : UpperStarWeilCompatible Λ φ h) :
    (geometricFiberWeilLowerStar Λ s).mapDerivedCategory ⋙
        (geometricFiberMapWeilLowerStar Λ φ h).rightDerivedFunctor ≅
      (φ)_*⟦Λ⟧.rightDerivedFunctor ⋙ (geometricFiberWeilLowerStar Λ t).mapDerivedCategory :=
  (Endofunctor.IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIsoOfForgetIso
      (lowerStarGeometricFiberMapCompFrobeniusIso Λ φ h) (geometricFiberWeilLowerStar Λ s)
      (T₀ := (s.geometricFiberProj)^*⟦Λ⟧) (Iso.refl _)).symm ≪≫
    Functor.rightDerivedFunctorNatIso (asIso (lowerStarGeometricFiberWeilBaseChange hc)).symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _

/-- Derived extension by zero of Weil objects and pullback to the geometric fibres:
`D(p_X^*) ⋙ D(weilExtensionByZero j) ≅ D(j_!) ⋙ D(p_Y^*)` for an open immersion `j`, given the
Frobenius compatibility of the pullback comparison of `j`. -/
noncomputable def geometricFiberWeilExtensionByZeroMapDerivedCategoryIso
    {j : X₀ ⟶ Y₀} [IsOpenImmersion j] {h : j ≫ t = s} (hc : UpperStarWeilCompatible Λ j h) :
    (geometricFiberWeilLowerStar Λ s).mapDerivedCategory ⋙
        (weilExtensionByZero Λ j h).mapDerivedCategory ≅
      (j)_!open⟦Λ⟧.mapDerivedCategory ⋙ (geometricFiberWeilLowerStar Λ t).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfIso (asIso (geometricFiberWeilExtensionByZeroBaseChange hc))

end Derived

section LowerShriek

variable {f : X₀ ⟶ Y₀}

/-- The direct image with compact support `Rf_! = Rḡ_* ∘ D(ī_!)` of condensed Weil objects over
the geometric fibres, attached to a compactification `X₀ ⟶[i] Z₀ ⟶[g] Y₀` of a morphism of
`k`-schemes; for `Λ = ℚ̲̄_ℓ` it is
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRightDerivedLowerShriek`. -/
noncomputable def weilRightDerivedLowerShriek (c : Compactification f) (h : f ≫ t = s) :
    DerivedCategory (Endofunctor.IsoAlgebra (lowerStar Λ s.geometricGaloisFrobenius.asIso.inv)) ⥤
      DerivedCategory (Endofunctor.IsoAlgebra (lowerStar Λ t.geometricGaloisFrobenius.asIso.inv)) :=
  (weilExtensionByZero Λ c.i (c.i_comp_g_comp h)).mapDerivedCategory ⋙
    (geometricFiberMapWeilLowerStar Λ c.g (rfl : c.g ≫ t = c.g ≫ t)).rightDerivedFunctor

variable {Λ}

/-- **The direct image with compact support of pulled-back Weil objects**: for a compactification
`c` of `f : X₀ ⟶ Y₀`, the condensed Weil `Rf̄_!` of the Weil objects `p_X^* M` with their canonical
Frobenius structure is `p_Y^* (Rf_! M)` with its canonical Frobenius structure:
`D(p_X^*) ⋙ Rf̄_! ≅ Rf_!(c) ⋙ D(p_Y^*)`, given the Frobenius compatibility of the pullback
comparisons of the open immersion and of the proper morphism of `c`. -/
noncomputable def geometricFiberWeilRightDerivedLowerShriekIso
    (c : Compactification f) (h : f ≫ t = s)
    (hi : UpperStarWeilCompatible Λ c.i (c.i_comp_g_comp h))
    (hg : UpperStarWeilCompatible Λ c.g (rfl : c.g ≫ t = c.g ≫ t)) :
    (geometricFiberWeilLowerStar Λ s).mapDerivedCategory ⋙ weilRightDerivedLowerShriek Λ c h ≅
      Rf_!(c)⟦Λ⟧ ⋙ (geometricFiberWeilLowerStar Λ t).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (geometricFiberWeilExtensionByZeroMapDerivedCategoryIso hi)
      _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (geometricFiberWeilRightDerivedLowerStarIso
      hg) ≪≫
    (Functor.associator _ _ _).symm

end LowerShriek

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over

/-- The new-model `Rf_!` of `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRightDerivedLowerShriek`
is the condensed Weil `Rf_!` of
`AlgebraicGeometry.ProEtale.CondensedRing.weilRightDerivedLowerShriek` for `Λ = ℚ̲̄_ℓ`. -/
lemma condensedRightDerivedLowerShriek_eq (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    (c : Compactification f) :
    condensedRightDerivedLowerShriek k₀ l f c =
      ProEtale.CondensedRing.weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj l) c
        (comp_over f _) :=
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
