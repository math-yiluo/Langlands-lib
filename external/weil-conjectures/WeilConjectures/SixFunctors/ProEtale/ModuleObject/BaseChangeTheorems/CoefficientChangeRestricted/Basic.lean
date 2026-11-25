/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicIntegers
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.Tactic.TransportModProofs

/-!
# Coefficient change for restricted base change maps: general coefficients

For a commutative square `sq : g' ≫ p' = p ≫ g` and a morphism `i : Z ⟶ Y'`, consider the
*restricted base change map* `Li^* (Lg^* Rp_* K ⟶ Rp'_* Lg'^* K)`, the base change map followed by
the pullback along `i` (for nearby cycles: the base change of `Rj_*` restricted to the special
fibre). This file shows that it is compatible with extension of scalars along any morphism of
coefficient rings `a : Λ ⟶ Λ'`:

* `ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app`:
  extension of scalars along `a` carries the restricted base change map at `K` to the one at
  `T K`, if the pushforwards commute with `T` at `K` and `Lg'^* K`;
* `ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat`:
  the analogue for a flat `a`.

The coefficient changes `𝔽_E ⟵ 𝒪_E ⟶ E ⟶ ℚ̄_ℓ` are in the other files of this directory and in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- A functor maps an isomorphism to an isomorphism (with the isomorphism as an explicit
hypothesis). -/
lemma isIso_map_of_isIso {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A B : C}
    {f : A ⟶ B} (h : IsIso f) : IsIso (F.map f) :=
  inferInstance

/-- If `H (α_A)` is an isomorphism and `A ≅ B`, then so is `H (α_B)`. -/
lemma isIso_map_app_of_iso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (α : F ⟶ G) (H : D ⥤ E) {A B : C} (e : A ≅ B) (h : IsIso (H.map (α.app A))) :
    IsIso (H.map (α.app B)) :=
  (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight α H) e).1 h

/-- A morphism isomorphic, as an arrow, to an isomorphism is an isomorphism. -/
lemma isIso_of_nonempty_arrowIso_of_isIso {C : Type*} [Category* C] {A B A' B' : C}
    {f : A ⟶ B} {g : A' ⟶ B'} (e : Nonempty (Arrow.mk f ≅ Arrow.mk g)) (hg : IsIso g) :
    IsIso f :=
  ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff e.some).2 hg

/-- Transport of an arrow isomorphism `F' f ≅ g` along a natural isomorphism
`F ⋙ G ≅ F' ⋙ G'`: `G (F f) ≅ G' g`. -/
lemma nonempty_arrowIso_map_map_of_iso {C D D' E : Type*} [Category* C] [Category* D]
    [Category* D'] [Category* E] {F : C ⥤ D} {G : D ⥤ E} {F' : C ⥤ D'} {G' : D' ⥤ E}
    (e : F ⋙ G ≅ F' ⋙ G') {A B : C} (f : A ⟶ B) {A' B' : D'} {g : A' ⟶ B'}
    (k : Nonempty (Arrow.mk (F'.map f) ≅ Arrow.mk g)) :
    Nonempty (Arrow.mk (G.map (F.map f)) ≅ Arrow.mk (G'.map g)) :=
  ⟨Arrow.isoMk' (G.map (F.map f)) (G'.map (F'.map f)) (e.app A) (e.app B)
    (e.hom.naturality f).symm ≪≫ G'.mapArrow.mapIso k.some⟩

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section General

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Extension of scalars and the restricted base change map**: for `a : Λ ⟶ Λ'` with extension
of scalars `T`, if the comparisons `T ∘ Rh_* ⟶ Rh_* ∘ T` are invertible at `K` for `h = p` and at
`Lg'^* K` for `h = p'`, then `T` of `Li^* BC_sq^Λ(K)` and `Li^* BC_sq^Λ'(T K)` are isomorphic
arrows. -/
theorem nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom a p).app K))
    (h₂ : IsIso ((derivedUpperStarExtendScalarsPushHom a p').app
      ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.map
        ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) ≅
      Arrow.mk ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)))) := by
  have k := nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat' a
    (derivedUpperStarExtendScalarsIsoCompCoherence a) sq K h₁ h₂
  exact nonempty_arrowIso_map_map_of_iso (F := L((i)^*⟦Λ⟧))
    (G := L(Mod.extendScalars (coefficientMap a Z)))
    (F' := L(Mod.extendScalars (coefficientMap a Y'))) (G' := L((i)^*⟦Λ'⟧))
    (derivedUpperStarExtendScalarsIso a i) _ (by exact_mod_proofs k)

/-- The restricted base change map with coefficients `Λ'` is invertible at `T K` if the one with
coefficients `Λ` is invertible at `K`, under the hypotheses of
`ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app`. -/
theorem isIso_map_baseChangeMap_app_extendScalars (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom a p).app K))
    (h₂ : IsIso ((derivedUpperStarExtendScalarsPushHom a p').app
      ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K)))
    (hK : IsIso ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) :
    IsIso ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  isIso_of_nonempty_arrowIso_map _ hK
    (nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app a sq i K h₁ h₂)

end General

section Flat

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Flat extension of scalars and the restricted base change map**: the analogue of
`ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app` for a
flat `a`, with the comparisons `derivedPushHom a`. -/
theorem nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat
    (H : DerivedPullIsoCompCoherence a) (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a p).app K))
    (h₂ : IsIso ((derivedPushHom a p').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.map
        ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) ≅
      Arrow.mk ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)))) := by
  have k := nonempty_arrowIso_map_exchangeRight_derivedExtendScalars a H sq K h₁ h₂
  exact nonempty_arrowIso_map_map_of_iso (F := L((i)^*⟦Λ⟧))
    (G := L(Mod.extendScalars (coefficientMap a Z)))
    (F' := L(Mod.extendScalars (coefficientMap a Y'))) (G' := L((i)^*⟦Λ'⟧))
    (derivedPullIso a i) _ (by exact_mod_proofs k)

/-- **Flat extension of scalars and the restricted base change map**: the analogue of
`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_extendScalars` for a flat `a`, with the
comparisons `derivedPushHom a`. -/
theorem isIso_map_baseChangeMap_app_derivedExtendScalars (H : DerivedPullIsoCompCoherence a)
    (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a p).app K))
    (h₂ : IsIso ((derivedPushHom a p').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K)))
    (hK : IsIso ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) :
    IsIso ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  isIso_of_nonempty_arrowIso_map _ hK
    (nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat a H sq i K h₁ h₂)

end Flat

section Transport

variable {Λ₁ Λ₂ Λ₃ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁]
  [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] [MonObj Λ₃] [IsCommMonObj Λ₃]
  (a : Λ₁ ⟶ Λ₂) [IsMonHom a] (b : Λ₂ ⟶ Λ₃) [IsMonHom b]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The restricted base change map with coefficients `Λ₃` is invertible at `K` as soon as it is
invertible at `T_b (T_a K₀)` for some `K₀` with `T_b (T_a K₀) ≅ K`. -/
lemma isIso_map_baseChangeMap_app_of_iso_extendScalars (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₁ X)))
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₃ X))}
    (e : Nonempty ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K₀) ≅ K))
    (h : IsIso ((L((i)^*⟦Λ₃⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ₃ p) (derivedUpperStarLowerStarAdjunction Λ₃ p')
      (pullbackSquareComparison Λ₃ sq)).app
        ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K₀))))) :
    IsIso ((L((i)^*⟦Λ₃⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ₃ p) (derivedUpperStarLowerStarAdjunction Λ₃ p')
      (pullbackSquareComparison Λ₃ sq)).app K)) :=
  isIso_map_app_of_iso _ _ e.some h

end Transport

end AlgebraicGeometry.ProEtale.CondensedRing
