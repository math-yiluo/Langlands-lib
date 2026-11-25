/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProperProjectionComp
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Basic
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityLaxMonoidal
import WeilConjectures.Tactic.ExactModProofs

/-!

# Base change over a change of base field and the lax tensor maps

For a commutative square `g' ≫ f = f' ≫ g` of schemes of finite type over possibly different
fields, the base change morphism `BC : Lg^* Rf_* ⟶ Rf'_* Lg'^*` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap`) is compatible with the lax tensor
maps of `Rf_*`, `Rf'_*` and the tensor maps of the pullbacks
(`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap_tensor`):
`Rf'_*(μ_{g'}) ∘ μ_{Rf'_*} ∘ (BC ⊗ BC) = BC ∘ Lg^*(μ_{Rf_*}) ∘ μ_g`.

It is the mate of the pullback comparison `Lg^* Lf'^* ≅ Lf^* Lg'^*`, which is monoidal, being
built from the composition isomorphisms of the derived pullbacks
(`ProEtale.CondensedRing.leftDerivedUpperStarComp_δ`); the abstract computation is
`CategoryTheory.Verdier.pushforwardExchange_tensor_aux`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Monoidal natural isomorphisms between composites -/

namespace CategoryTheory.Functor

variable {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory E']

/-- A transformation `θ : G₁ ⋙ F₂ ⟶ F₁ ⋙ G₂` between composites of monoidal functors which is
compatible with the comultiplications of the composites is compatible with the tensor maps in the
mixed form `F₂(μ_{G₁}) ≫ θ ≫ G₂(δ_{F₁}) = δ_{F₂} ≫ (θ ⊗ θ) ≫ μ_{G₂}`. -/
lemma map_μ_comp_app_comp_map_δ_of_δ {G₁ : C ⥤ D} {F₂ : D ⥤ E} {F₁ : C ⥤ E'} {G₂ : E' ⥤ E}
    [G₁.Monoidal] [F₂.Monoidal] [F₁.Monoidal] [G₂.Monoidal] (θ : G₁ ⋙ F₂ ⟶ F₁ ⋙ G₂)
    (U V : C)
    (h : OplaxMonoidal.δ (G₁ ⋙ F₂) U V ≫ (θ.app U ⊗ₘ θ.app V) =
      θ.app (U ⊗ V) ≫ OplaxMonoidal.δ (F₁ ⋙ G₂) U V) :
    F₂.map (LaxMonoidal.μ G₁ U V) ≫ θ.app (U ⊗ V) ≫ G₂.map (OplaxMonoidal.δ F₁ U V) =
      OplaxMonoidal.δ F₂ _ _ ≫ (θ.app U ⊗ₘ θ.app V) ≫ LaxMonoidal.μ G₂ _ _ := by
  simp only [OplaxMonoidal.comp_δ, comp_obj, Category.assoc] at h
  rw [← cancel_epi (F₂.map (OplaxMonoidal.δ G₁ U V)), ← F₂.map_comp_assoc, Monoidal.δ_μ,
    F₂.map_id, Category.id_comp, ← cancel_mono (OplaxMonoidal.δ G₂ (F₁.obj U) (F₁.obj V))]
  simp only [Category.assoc, Monoidal.μ_δ]
  simpa using h.symm

/-- A composite `c₁⁻¹ ≫ e ≫ c₂` of transformations of oplax monoidal functors compatible with the
comultiplications is compatible with the comultiplications. -/
lemma δ_comp_tensorHom_of_eq_inv_comp {F₀ F₁ F₂ F₃ : C ⥤ D} [OplaxMonoidal F₀]
    [OplaxMonoidal F₁] [OplaxMonoidal F₂] [OplaxMonoidal F₃] (c₁ : F₁ ≅ F₀) (e : F₁ ⟶ F₂)
    (c₂ : F₂ ≅ F₃) (θ : F₀ ⟶ F₃) (hθ : θ = c₁.inv ≫ e ≫ c₂.hom) (K M : C)
    (h₁ : OplaxMonoidal.δ F₁ K M ≫ (c₁.hom.app K ⊗ₘ c₁.hom.app M) =
      c₁.hom.app (K ⊗ M) ≫ OplaxMonoidal.δ F₀ K M)
    (h₂ : OplaxMonoidal.δ F₂ K M ≫ (c₂.hom.app K ⊗ₘ c₂.hom.app M) =
      c₂.hom.app (K ⊗ M) ≫ OplaxMonoidal.δ F₃ K M)
    (h₃ : OplaxMonoidal.δ F₁ K M ≫ (e.app K ⊗ₘ e.app M) = e.app (K ⊗ M) ≫ OplaxMonoidal.δ F₂ K M) :
    OplaxMonoidal.δ F₀ K M ≫ (θ.app K ⊗ₘ θ.app M) = θ.app (K ⊗ M) ≫ OplaxMonoidal.δ F₃ K M := by
  subst hθ
  have h₁' : OplaxMonoidal.δ F₀ K M ≫ (c₁.inv.app K ⊗ₘ c₁.inv.app M) =
      c₁.inv.app (K ⊗ M) ≫ OplaxMonoidal.δ F₁ K M := by
    rw [← cancel_epi (c₁.hom.app (K ⊗ M)), ← reassoc_of% h₁]
    simp
  simp only [NatTrans.comp_app, Category.assoc]
  rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom, reassoc_of% h₁', reassoc_of% h₃,
    h₂]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-! ### The pullback comparison is monoidal -/

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The identification `L(h₁)^* = L(h₂)^*` for equal morphisms `h₁ = h₂` is compatible with the
comultiplications. -/
lemma δ_comp_eqToIso_hom_app {X Y : Scheme.{u}} {h₁ h₂ : X ⟶ Y} (w : h₁ = h₂)
    (e : L((h₁)^*⟦Λ⟧) = L((h₂)^*⟦Λ⟧))
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    Functor.OplaxMonoidal.δ L((h₁)^*⟦Λ⟧) K M ≫ ((eqToIso e).hom.app K ⊗ₘ (eqToIso e).hom.app M) =
      (eqToIso e).hom.app (K ⊗ M) ≫ Functor.OplaxMonoidal.δ L((h₂)^*⟦Λ⟧) K M := by
  subst w
  simp

/-- **The pullback comparison is monoidal**: for a commutative square `g' ≫ p = p' ≫ g`, the
comparison `θ : Lg^* ⋙ Lp'^* ≅ Lp^* ⋙ Lg'^*`
(`ProEtale.CondensedRing.pullbackSquareComparison`) is compatible with the comultiplications of
the composites. -/
lemma δ_comp_pullbackSquareComparison_hom_app {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g)
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    Functor.OplaxMonoidal.δ (L((g)^*⟦Λ⟧) ⋙ L((p')^*⟦Λ⟧)) K M ≫
        ((pullbackSquareComparison Λ sq).hom.app K ⊗ₘ (pullbackSquareComparison Λ sq).hom.app M) =
      (pullbackSquareComparison Λ sq).hom.app (K ⊗ M) ≫
        Functor.OplaxMonoidal.δ (L((p)^*⟦Λ⟧) ⋙ L((g')^*⟦Λ⟧)) K M := by
  refine Functor.δ_comp_tensorHom_of_eq_inv_comp (leftDerivedUpperStarComp Λ p' g)
    (eqToIso (by rw [sq.w])).hom (leftDerivedUpperStarComp Λ g' p) _ ?_ K M ?_ ?_ ?_
  · rfl
  · exact leftDerivedUpperStarComp_δ Λ p' g K M
  · exact leftDerivedUpperStarComp_δ Λ g' p K M
  · exact δ_comp_eqToIso_hom_app Λ sq.w.symm _ K M

/-- The base change morphism is the mate of the pullback comparison, on the ambient derived
categories. -/
lemma map_baseChangeMap_app_comp_counit_ambient {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    L((p')^*⟦Λ⟧).map ((baseChangeMap Λ sq).app K) ≫
        (derivedUpperStarLowerStarAdjunction Λ p').counit.app (L((g')^*⟦Λ⟧).obj K) =
      (pullbackSquareComparison Λ sq).hom.app (R((p)_*⟦Λ⟧).obj K) ≫
        L((g')^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ p).counit.app K) :=
  Adjunction.exchangeRight_app_comp_counit' (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)
    (baseChangeMap Λ sq) rfl K

end Ambient

/-! ### The base change morphism and the lax tensor maps -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y'.left ⟶ Y.left} {g' : X'.left ⟶ X.left}

/-- The pullback comparison `Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*` on bounded constructible complexes for a
commutative square `g' ≫ f = f' ≫ g` of schemes of finite type over possibly different fields: the
restriction of `ProEtale.CondensedRing.pullbackSquareComparison`. -/
noncomputable def boundedConstructiblePullbackComparisonOfMap (sq : CommSq g' f'.left f.left g) :
    boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g' :=
  NearbyCyclesModel.liftExchange (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq).hom
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g' K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f K)

/-- `CategoryTheory.Adjunction.exchangeRight_app_comp_counit` for the restrictions to bounded
constructible complexes, for arbitrary ambient transformations `θ` and `bc` with the mate
relation; they are kept abstract so that the kernel never unfolds the pullback comparison and the
base change morphism. -/
private lemma map_liftExchange_app_comp_counit_aux
    (θ : L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((g')^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (bc : R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((g')^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ R((f'.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (h : ∀ K, L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map (bc.app K) ≫
        (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f'.left).counit.app
          (L((g')^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K) =
      θ.app (R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K) ≫
        L((g')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).counit.app
            K))
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        ((NearbyCyclesModel.liftExchange bc
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g' K.obj K.property) :
            boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ (X := Y)
              (Y := Y') g ⟶ boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g' ⋙
                boundedConstructibleLowerStar ℓ f').app A) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f').counit.app
          ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').obj A) =
      (NearbyCyclesModel.liftExchange θ
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g' K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f' K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f K) :
            boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g ⋙
              boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⟶
            boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
              boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').app
          ((boundedConstructibleLowerStar ℓ f).obj A) ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app A) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom,
    boundedConstructibleUpperStarOfMap_map, ObjectProperty.homMk_hom,
    NearbyCyclesModel.liftExchange_app_hom]
  cast_proofs h A.obj

/-- The base change morphism is the mate of the pullback comparison: compatibility with the
counits of `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
lemma map_boundedConstructibleBaseChangeOfMap_app_comp_counit (sq : CommSq g' f'.left f.left g)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        ((boundedConstructibleBaseChangeOfMap ℓ sq).app A) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f').counit.app
          ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').obj A) =
      (boundedConstructiblePullbackComparisonOfMap ℓ sq).app
          ((boundedConstructibleLowerStar ℓ f).obj A) ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app A) := by
  have h := map_liftExchange_app_comp_counit_aux ℓ
    (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq).hom
    (baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq)
    (map_baseChangeMap_app_comp_counit_ambient (Profinite.padicAlgClRingObj ℓ) sq) A
  unfold boundedConstructibleBaseChangeOfMap boundedConstructiblePullbackComparisonOfMap
  cast_proofs h

/-- The monoidality of the restriction to bounded constructible complexes of an arbitrary
comparison `θ`, deduced from that of `θ`; it is kept abstract so that the kernel never unfolds
the pullback comparison. -/
private lemma map_μ_comp_liftExchange_app_aux
    (θ : L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ L((g')^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (hθ : ∀ K M, Functor.OplaxMonoidal.δ (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((f'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)) K M ≫ (θ.app K ⊗ₘ θ.app M) =
      θ.app (K ⊗ M) ≫ Functor.OplaxMonoidal.δ (L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((g')^*⟦Profinite.padicAlgClRingObj ℓ⟧)) K M)
    (α : boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g')
    (hα : α = NearbyCyclesModel.liftExchange θ
      (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property)
      (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g' K.obj K.property)
      (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f' K)
      (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f K))
    (U V : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g) U V) ≫
        α.app (U ⊗ V) ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').map
          (Functor.OplaxMonoidal.δ
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) U V) =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
          _ _ ≫ (α.app U ⊗ₘ α.app V) ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g') _ _ := by
  subst hα
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    μ_boundedConstructibleUpperStarOfMap, ObjectProperty.homMk_hom,
    boundedConstructibleUpperStarOfMap_map, boundedConstructibleUpperStar_δ_hom,
    ObjectProperty.tensorHom_hom', NearbyCyclesModel.liftExchange_app_hom]
  exact Functor.map_μ_comp_app_comp_map_δ_of_δ θ U.obj V.obj (hθ U.obj V.obj)

/-- The pullback comparison on bounded constructible complexes is monoidal, in the mixed form of
`CategoryTheory.Verdier.pushforwardExchange_tensor_aux`. -/
lemma map_μ_comp_boundedConstructiblePullbackComparisonOfMap_app
    (sq : CommSq g' f'.left f.left g) (U V : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g) U V) ≫
        (boundedConstructiblePullbackComparisonOfMap ℓ sq).app (U ⊗ V) ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').map
          (Functor.OplaxMonoidal.δ
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) U V) =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
          _ _ ≫
        ((boundedConstructiblePullbackComparisonOfMap ℓ sq).app U ⊗ₘ
          (boundedConstructiblePullbackComparisonOfMap ℓ sq).app V) ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g') _ _ :=
  map_μ_comp_liftExchange_app_aux ℓ (pullbackSquareComparison _ sq).hom
    (δ_comp_pullbackSquareComparison_hom_app _ sq)
    (boundedConstructiblePullbackComparisonOfMap ℓ sq)
    rfl U V

/-- `CategoryTheory.Verdier.pushforwardExchange_tensor_aux` for the restricted functors, for
arbitrary transformations `α` (pullback comparison) and `χ` (its mate); they are kept abstract so
that the kernel never unfolds them. -/
private lemma pushforwardExchange_tensor_restricted_aux
    (α : boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g')
    (χ : boundedConstructibleLowerStar ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g'
        ⋙ boundedConstructibleLowerStar ℓ f')
    (hχ : ∀ A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map (χ.app A) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f').counit.app
          ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').obj A) =
      α.app ((boundedConstructibleLowerStar ℓ f).obj A) ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app A))
    (hα : ∀ U V : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g) U V) ≫
        α.app (U ⊗ V) ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g').map
          (Functor.OplaxMonoidal.δ
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) U V) =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
          _ _ ≫ (α.app U ⊗ₘ α.app V) ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g') _ _)
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (χ.app A ⊗ₘ χ.app B) ≫
      (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f';
        Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f') _ _) ≫
      (boundedConstructibleLowerStar ℓ f').map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g') A B) =
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g) _ _ ≫
      (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g).map
        (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f;
          Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f) A B) ≫
      χ.app (A ⊗ B) :=
  Verdier.pushforwardExchange_tensor_aux (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f')
    (fun U V ↦ Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g')
      U V)
    (fun U V ↦ Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g)
      U V)
    (fun x y ↦ Functor.LaxMonoidal.μ_natural _ x y) α χ hχ hα A B

/-- **Base change is compatible with the lax tensor maps**: for a commutative square
`g' ≫ f = f' ≫ g` of schemes of finite type over possibly different fields,
`Rf'_*(μ_{g'}) ∘ μ_{Rf'_*} ∘ (BC ⊗ BC) = BC ∘ Lg^*(μ_{Rf_*}) ∘ μ_g`, by
`CategoryTheory.Verdier.pushforwardExchange_tensor_aux`. -/
theorem boundedConstructibleBaseChangeOfMap_tensor (sq : CommSq g' f'.left f.left g)
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleBaseChangeOfMap ℓ sq).app A ⊗ₘ
        (boundedConstructibleBaseChangeOfMap ℓ sq).app B) ≫
      (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f';
        Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f') _ _) ≫
      (boundedConstructibleLowerStar ℓ f').map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g') A B) =
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g) _ _ ≫
      (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') g).map
        (letI := boundedConstructibleLowerStarLaxMonoidal ℓ f;
          Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ f) A B) ≫
      (boundedConstructibleBaseChangeOfMap ℓ sq).app (A ⊗ B) :=
  pushforwardExchange_tensor_restricted_aux ℓ (boundedConstructiblePullbackComparisonOfMap ℓ sq)
    (boundedConstructibleBaseChangeOfMap ℓ sq)
    (map_boundedConstructibleBaseChangeOfMap_app_comp_counit ℓ sq)
    (map_μ_comp_boundedConstructiblePullbackComparisonOfMap_app ℓ sq) A B

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
