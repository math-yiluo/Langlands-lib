/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrict
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFac
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportDerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportDerivedBaseChangeOfCommSq

/-!
# The integral base-change morphism and the derived reduction

For a cartesian square of schemes separated and of finite type over `k` and
`K₀ ∈ Dᵇc(X)⟦𝒪_E⟧`, the first derived reduction of the integral base-change morphism `BC_sq(K₀)`
and the pro-étale base-change morphism with coefficients `𝔽_E` at the first derived reduction of
`K₀` are isomorphic arrows
(`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_boundedConstructibleBaseChange`); this
file collects the ingredients of its proof.

The proof combines:
- the identification of `BC_sq(K₀)` with the exchange morphism of the pullback comparison on the
  ambient derived categories (`Adjunction.exchangeRight_restrictFullyFaithful_app_hom`);
- the transfer of exchange morphisms along the non-flat coefficient change `𝒪_E ⟶ 𝔽_E`
  (`ProEtale.CondensedRing.nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat'`),
  whose (Push) comparisons are invertible on bounded below complexes
  (`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`);
- the transport along residue field module sheaves
  (`ProEtale.nonempty_arrowIso_map_exchangeRight_residueField_derivedBaseChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- A nonempty family of isomorphisms from the image of a morphism `y` gives one from the image of
any morphism equal to `y`. -/
lemma nonempty_arrowIso_map_of_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B : C} {x y : A ⟶ B} (h : x = y) {Z : Arrow D}
    (e : Nonempty (Arrow.mk (F.map y) ≅ Z)) : Nonempty (Arrow.mk (F.map x) ≅ Z) := by
  subst h
  exact e

/-- Isomorphisms of arrows from `F.map x` and from the image under `G` of the target give an
isomorphism of arrows from `(F ⋙ G).map x`. -/
lemma nonempty_arrowIso_comp_map_of_nonempty {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (F : C ⥤ D) (G : D ⥤ E) {A B : C} {x : A ⟶ B} {Y : Arrow D} {Z : Arrow E}
    (e₁ : Nonempty (Arrow.mk (F.map x) ≅ Y)) (e₂ : Nonempty (G.mapArrow.obj Y ≅ Z)) :
    Nonempty (Arrow.mk ((F ⋙ G).map x) ≅ Z) := by
  obtain ⟨a⟩ := e₁
  obtain ⟨b⟩ := e₂
  exact ⟨G.mapArrow.mapIso a ≪≫ b⟩

/-- Isomorphisms of arrows from `F.map x` to `y` and from `G.map y` give an isomorphism of
arrows from `(F ⋙ G).map x`. -/
lemma nonempty_arrowIso_comp_map_of_nonempty' {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (F : C ⥤ D) (G : D ⥤ E) {A B : C} {x : A ⟶ B} {A' B' : D} (y : A' ⟶ B')
    {Z : Arrow E} (e₁ : Nonempty (Arrow.mk (F.map x) ≅ Arrow.mk y))
    (e₂ : Nonempty (Arrow.mk (G.map y) ≅ Z)) : Nonempty (Arrow.mk ((F ⋙ G).map x) ≅ Z) := by
  obtain ⟨a⟩ := e₁
  obtain ⟨b⟩ := e₂
  exact ⟨G.mapArrow.mapIso a ≪≫ b⟩

/-- A form of `nonempty_arrowIso_comp_map_of_nonempty'` for functors `H = F ⋙ G` and
`H' = F' ⋙ G'` given up to equality, the target being a component of a natural transformation
at an object `H'.obj K`. -/
lemma nonempty_arrowIso_map_of_eq_comp {C D E C' D' E' : Type*} [Category* C] [Category* D]
    [Category* E] [Category* C'] [Category* D'] [Category* E'] (F : C ⥤ D) (G : D ⥤ E)
    (H : C ⥤ E) (hH : H = F ⋙ G) (F' : C' ⥤ D') (G' : D' ⥤ E') (H' : C' ⥤ E')
    (hH' : H' = F' ⋙ G') {S T : E' ⥤ E} (α : S ⟶ T) (K : C') {A B : C} {x : A ⟶ B}
    {A' B' : D} (y : A' ⟶ B') (e₁ : Nonempty (Arrow.mk (F.map x) ≅ Arrow.mk y))
    (e₂ : Nonempty (Arrow.mk (G.map y) ≅ Arrow.mk (α.app (G'.obj (F'.obj K))))) :
    Nonempty (Arrow.mk (H.map x) ≅ Arrow.mk (α.app (H'.obj K))) := by
  subst hH hH'
  exact nonempty_arrowIso_comp_map_of_nonempty' F G y e₁ e₂

namespace Adjunction

variable {B A B' A' : Type*} [Category* B] [Category* A] [Category* B'] [Category* A']
  {PB : ObjectProperty B} {PA : ObjectProperty A} {PB' : ObjectProperty B'}
  {PA' : ObjectProperty A'}
  {lf : B ⥤ A} {rf : A ⥤ B} {lf' : B' ⥤ A'} {rf' : A' ⥤ B'} {g : B ⥤ B'} {g' : A ⥤ A'}

/-- If `β` is the exchange morphism of restricted adjunctions of an isomorphism `θ` which is `t`
on the underlying objects, then isomorphisms of arrows from the image of the exchange morphism
of `t` give isomorphisms of arrows from the image of `β` on the underlying objects. -/
theorem nonempty_arrowIso_map_ι_map_app_of_eq_exchangeRight
    (ad : lf ⊣ rf) (ad' : lf' ⊣ rf') (t : g ⋙ lf' ≅ lf ⋙ g')
    (hlf : ∀ K : PB.FullSubcategory, PA ((PB.ι ⋙ lf).obj K))
    (hrf : ∀ K : PA.FullSubcategory, PB ((PA.ι ⋙ rf).obj K))
    (hlf' : ∀ K : PB'.FullSubcategory, PA' ((PB'.ι ⋙ lf').obj K))
    (hrf' : ∀ K : PA'.FullSubcategory, PB' ((PA'.ι ⋙ rf').obj K))
    (hg : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ g).obj K))
    (hg' : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ g').obj K))
    (θ : PB'.lift (PB.ι ⋙ g) hg ⋙ PA'.lift (PB'.ι ⋙ lf') hlf' ≅
      PA.lift (PB.ι ⋙ lf) hlf ⋙ PA'.lift (PA.ι ⋙ g') hg')
    (hθ : ∀ K, (θ.hom.app K).hom = t.hom.app K.obj)
    (β : PB.lift (PA.ι ⋙ rf) hrf ⋙ PB'.lift (PB.ι ⋙ g) hg ⟶
      PA'.lift (PA.ι ⋙ g') hg' ⋙ PB'.lift (PA'.ι ⋙ rf') hrf')
    (hβ : β = exchangeRight
        (ad.restrictFullyFaithful PB.fullyFaithfulι PA.fullyFaithfulι
          (PA.liftCompιIso (PB.ι ⋙ lf) hlf).symm (PB.liftCompιIso (PA.ι ⋙ rf) hrf).symm)
        (ad'.restrictFullyFaithful PB'.fullyFaithfulι PA'.fullyFaithfulι
          (PA'.liftCompιIso (PB'.ι ⋙ lf') hlf').symm (PB'.liftCompιIso (PA'.ι ⋙ rf') hrf').symm)
        θ)
    {T : Type*} [Category* T] (F : B' ⥤ T) (K : PA.FullSubcategory) {Z : Arrow T}
    (e : Nonempty (Arrow.mk (F.map ((exchangeRight ad ad' t).app K.obj)) ≅ Z)) :
    Nonempty (Arrow.mk (F.map (PB'.ι.map (β.app K))) ≅ Z) := by
  subst hβ
  rw [ObjectProperty.ι_map,
    exchangeRight_restrictFullyFaithful_app_hom ad ad' t hlf hrf hlf' hrf' hg hg' θ hθ K]
  exact e

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- the objects of the bounded constructible and of the ambient derived categories are compared
/-- A public copy of the private lemma `pullbackSquareComparison_hom_app_hom_aux` of
`CoefficientChangeCubeBoundedConstructible`: on the ambient derived categories, the pullback
comparison on bounded constructible complexes is the pullback comparison of the underlying
square, in the `ObjectProperty.lift` presentation of
`Adjunction.exchangeRight_restrictFullyFaithful_app_hom`. -/
lemma pullbackSquareComparison_hom_app_hom_lift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (sq : CommSq g' f' f g)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ((Iso.hom (X := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((g.left)^*⟦Λ⟧))
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ g K) ⋙
       (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f'.left)^*⟦Λ⟧))
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f' K))
      (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K) ⋙
       (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((g'.left)^*⟦Λ⟧))
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ g' K))
      (boundedConstructiblePullbackSquareComparison Λ ℓ sq)).app K).hom =
      (pullbackSquareComparison Λ
        (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left f'.left f.left g.left)).hom.app
        K.obj := by
  have hinv (p : X' ⟶ Y') (q : Y' ⟶ Y) :
      ((boundedConstructibleUpperStarComp Λ ℓ p q).inv.app K).hom =
        (leftDerivedUpperStarComp Λ p.left q.left).inv.app K.obj := by
    simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
      ObjectProperty.liftCompιIso]
  have e {A₁ A₂ : Dᵇc(X'.left)⟦Λ⟧} (h : A₁ = A₂) :
      (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
    subst h
    rfl
  simp only [boundedConstructiblePullbackSquareComparison_hom_app Λ ℓ sq K,
    pullbackSquareComparison_hom_app Λ _ K.obj, ObjectProperty.FullSubcategory.comp_hom,
    hinv f' g, boundedConstructibleUpperStarComp_hom_app_hom Λ ℓ g' f K, e]

end AlgebraicGeometry.ProEtale.CondensedRing
