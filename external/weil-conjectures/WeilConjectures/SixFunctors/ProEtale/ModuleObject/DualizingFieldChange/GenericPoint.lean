/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.SmoothProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BaseChangePaste
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
import WeilConjectures.Tactic.ExactModProofs

/-!

# Base change of exceptional inverse images along generic points

Let `b = i ≫ p : Z ⟶ Y ⟶ P` be a projective morphism of separated schemes of finite type over a
field `k₁`: a closed immersion `i` followed by a proper morphism `p` smooth of pure relative
dimension `d` (for instance `Y = P × ℙᴺ`). Let `g : P' ⟶ P` be a base map out of a scheme `P'`
over a field `L` with `P' ≅ Spec L` (for instance `P' = Spec L`), factoring as
```
P' ≅ Spec L --πₛ--> Spec K₀ --η--> P
```
with `πₛ` given by a field extension `L/K₀` and `η` weakly étale (for instance the inclusion of the
generic point of an integral `P`, `K₀ = κ(P)`, which is a limit of open immersions). This file
proves that the base change map `γ : π^* Rb^! ⟶ Rb'^! g^*` of the exceptional inverse image
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) of any cartesian square `π ≫ b = b' ≫ g` is
an isomorphism of functors
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_projective_of_comp_eq`,
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_projective_of_isIso_hom`).

## Main results

- `ProEtale.CondensedRing.upperShriekBaseChangeOfMap_app_paste`: the **horizontal composition
  law** of the base change maps: for horizontally pasted cartesian squares over three fields,
  `γ_outer` is `πZ'^* γ₁` followed by `γ₂`, through the composition isomorphisms of the pullbacks
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarOfMapComp`). It comes from the horizontal
  pasting of the proper base change maps
  (`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap_app_paste`).
- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_point`: for a proper `K₀`-scheme `Z`
  with structure morphism `f` and its base change `f'` along a field extension `L/K₀`, `γ` is an
  isomorphism of functors.
- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_projective_of_genericPoint`:
  the main result, with the intermediate base change `Z₀ ⟶ Y₀ ⟶ Spec K₀` given.
- `AlgebraicGeometry.affineLineGenericPoint`: the generic point `Spec k(x) ⟶ 𝔸¹_k`, weakly étale
  (`AlgebraicGeometry.weaklyEtale_affineLineGenericPoint`); more generally
  `Scheme.weaklyEtale_fromSpecStalk`.
- `AlgebraicGeometry.traitSlicePoint_eq_comp_affineLineGenericPoint`,
  `AlgebraicGeometry.traitGenericSlice_eq_comp_affineLineGenericPoint`: for `x` transcendental,
  the slice point `Spec K ⟶ 𝔸¹_{k'}` and the generic slice `Spec Frac K⟦t⟧ ⟶ 𝔸¹_η` factor as a
  field extension followed by the generic point of the line. These are the factorizations of the
  base maps of the slices of a model with a coordinate.

## Proof

*Composition law.* The base change map of a proper `f` is the mate of the inverse proper base
change isomorphism, i.e. the exchange morphism `CategoryTheory.Adjunction.exchangeRight` of
`Rf_* ⊣ Rf^!` (`CategoryTheory.Adjunction.exchangeRight_eq_mateEquiv`), and exchange morphisms
paste (`CategoryTheory.Adjunction.exchangeRight_app_paste`) as soon as the proper base change maps
do; these are the restrictions of the ambient base change maps, which paste
(`ProEtale.CondensedRing.pullbackSquareComparison_paste`).

*Along `η`.* `b = i ≫ p` with `i` a closed immersion and `p` smooth proper: weakly étale base
change of the closed exceptional inverse image
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale`) and of the smooth
one (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale`),
composed by `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app`.

*Along the field extension.* Over the point `Spec K₀` the base change map at the unit is the
comparison of the dualizing complexes of the proper scheme `Z₀` up to that of the point
(`ProEtale.CondensedRing.dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap`), both
invertible (`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_fieldExtension`). For any
`N` on the point, `N` is dualizable, so `Rf^! N ≅ f^* N ⊗ Rf^! ℚ̄_ℓ` and the two sides of
`γ(N)` are isomorphic (`ProEtale.CondensedRing.upperShriekBaseChangeIsoPoint`); `Rf'_* γ(N)` is
invertible since pullback from a point commutes with internal homs, and the endomorphism trick
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_iso`) concludes.

## Implementation notes

As in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Closed`, the
pasting law on bounded constructible complexes is proved for arbitrary ambient transformations and
instantiated once with `cast_proofs`, the kernel timing out otherwise.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The coefficient ring `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

section Paste

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ k₃ : Type u} [Field k₁] [Field k₂] [Field k₃]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃).Prime] [Fact (ringChar k₃ ≠ ℓ)]

/-- The composition isomorphism `L(h ≫ g)^* ≅ Lg^* ⋙ Lh^*` of the pullbacks of bounded
constructible complexes along morphisms of schemes over possibly different fields: the restriction
of `ProEtale.CondensedRing.leftDerivedUpperStarComp`. -/
noncomputable def boundedConstructibleUpperStarOfMapComp {X : Over (Spec (.of k₁))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] {W : Over (Spec (.of k₃))} [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] [IsSeparated W.hom] (g : Y.left ⟶ X.left) (h : W.left ⟶ Y.left) :
    boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := W) (h ≫ g) ≅
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := W) h :=
  NatIso.ofComponents
    (fun A ↦ ObjectProperty.isoMk _ ((leftDerivedUpperStarComp 𝐐 h g).app A.obj))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (leftDerivedUpperStarComp 𝐐 h g).hom.naturality f.hom)

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₂).Prime] [Fact (ringChar k₃).Prime]
  [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar k₃ ≠ ℓ)] in
/-- The composition isomorphism of pullbacks is that of the ambient derived categories. -/
@[simp]
lemma boundedConstructibleUpperStarOfMapComp_hom_app_hom {X : Over (Spec (.of k₁))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] {W : Over (Spec (.of k₃))} [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] [IsSeparated W.hom] (g : Y.left ⟶ X.left) (h : W.left ⟶ Y.left)
    (A : Dᵇc(X.left)⟦𝐐⟧) :
    ((boundedConstructibleUpperStarOfMapComp ℓ g h).hom.app A).hom =
      (leftDerivedUpperStarComp 𝐐 h g).hom.app A.obj :=
  rfl

variable {Z P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {Z'' P'' : Over (Spec (.of k₃))} [LocallyOfFiniteType Z''.hom] [QuasiCompact Z''.hom]
  [IsSeparated Z''.hom] [LocallyOfFiniteType P''.hom] [QuasiCompact P''.hom]
  [IsSeparated P''.hom]
  {f : Z ⟶ P} {f' : Z' ⟶ P'} {f'' : Z'' ⟶ P''}
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left} {πP' : P''.left ⟶ P'.left}
  {πZ' : Z''.left ⟶ Z'.left}

/-- The horizontal pasting law on bounded constructible complexes, for arbitrary ambient
transformations `χ₁`, `χ₂`, `χ` satisfying the ambient law; they are kept abstract so that the
kernel never unfolds the base change morphisms. -/
private lemma liftExchange_paste_horiz_aux
    (χ₁ : R((f.left)_*⟦𝐐⟧) ⋙ L((πP)^*⟦𝐐⟧) ⟶ L((πZ)^*⟦𝐐⟧) ⋙ R((f'.left)_*⟦𝐐⟧))
    (χ₂ : R((f'.left)_*⟦𝐐⟧) ⋙ L((πP')^*⟦𝐐⟧) ⟶ L((πZ')^*⟦𝐐⟧) ⋙ R((f''.left)_*⟦𝐐⟧))
    (χ : R((f.left)_*⟦𝐐⟧) ⋙ L((πP' ≫ πP)^*⟦𝐐⟧) ⟶ L((πZ' ≫ πZ)^*⟦𝐐⟧) ⋙ R((f''.left)_*⟦𝐐⟧))
    (h : ∀ K, (leftDerivedUpperStarComp 𝐐 πP' πP).hom.app (R((f.left)_*⟦𝐐⟧).obj K) ≫
      L((πP')^*⟦𝐐⟧).map (χ₁.app K) ≫ χ₂.app (L((πZ)^*⟦𝐐⟧).obj K) =
      χ.app K ≫ R((f''.left)_*⟦𝐐⟧).map ((leftDerivedUpperStarComp 𝐐 πZ' πZ).hom.app K))
    (K : Dᵇc(Z.left)⟦𝐐⟧) :
    (boundedConstructibleUpperStarOfMapComp ℓ πP πP').hom.app
        ((boundedConstructibleLowerStar ℓ f).obj K) ≫
      (boundedConstructibleUpperStarOfMap ℓ πP').map
        ((NearbyCyclesModel.liftExchange χ₁
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πP K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πZ K.obj K.property) :
            boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πP ⟶
              boundedConstructibleUpperStarOfMap ℓ πZ ⋙ boundedConstructibleLowerStar ℓ f').app
          K) ≫
      (NearbyCyclesModel.liftExchange χ₂
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f' K)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f'' K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πP' K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πZ' K.obj
            K.property) :
            boundedConstructibleLowerStar ℓ f' ⋙ boundedConstructibleUpperStarOfMap ℓ πP' ⟶
              boundedConstructibleUpperStarOfMap ℓ πZ' ⋙ boundedConstructibleLowerStar ℓ f'').app
        ((boundedConstructibleUpperStarOfMap ℓ πZ).obj K) =
    (NearbyCyclesModel.liftExchange χ
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f'' K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (πP' ≫ πP) K.obj
            K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (πZ' ≫ πZ) K.obj
            K.property) :
            boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ (πP' ≫ πP) ⟶
              boundedConstructibleUpperStarOfMap ℓ (πZ' ≫ πZ) ⋙
                boundedConstructibleLowerStar ℓ f'').app K ≫
      (boundedConstructibleLowerStar ℓ f'').map
        ((boundedConstructibleUpperStarOfMapComp ℓ πZ πZ').hom.app K) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, NearbyCyclesModel.liftExchange_app_hom,
    boundedConstructibleUpperStarOfMap_map, ObjectProperty.homMk_hom,
    boundedConstructibleUpperStarOfMapComp_hom_app_hom, boundedConstructibleLowerStar_map_hom]
  exact h K.obj

/-- **Horizontal pasting of base change maps** on bounded constructible complexes: for two
horizontally pasted commutative squares
```
Z'' --πZ'--> Z' --πZ--> Z
 |f''         |f'        |f
 v            v          v
P'' --πP'--> P' --πP--> P
```
the base change map `L(πP' ≫ πP)^* Rf_* ⟶ Rf''_* L(πZ' ≫ πZ)^*` of the outer square is the pasting
of those of the two squares, through the composition isomorphisms of the pullbacks. -/
lemma boundedConstructibleBaseChangeOfMap_app_paste (sq₁ : CommSq πZ f'.left f.left πP)
    (sq₂ : CommSq πZ' f''.left f'.left πP') (sq : CommSq (πZ' ≫ πZ) f''.left f.left (πP' ≫ πP))
    (K : Dᵇc(Z.left)⟦𝐐⟧) :
    (boundedConstructibleUpperStarOfMapComp ℓ πP πP').hom.app
        ((boundedConstructibleLowerStar ℓ f).obj K) ≫
      (boundedConstructibleUpperStarOfMap ℓ πP').map
        ((boundedConstructibleBaseChangeOfMap ℓ sq₁).app K) ≫
      (boundedConstructibleBaseChangeOfMap ℓ sq₂).app
        ((boundedConstructibleUpperStarOfMap ℓ πZ).obj K) =
    (boundedConstructibleBaseChangeOfMap ℓ sq).app K ≫
      (boundedConstructibleLowerStar ℓ f'').map
        ((boundedConstructibleUpperStarOfMapComp ℓ πZ πZ').hom.app K) := by
  have hamb : ∀ K, (leftDerivedUpperStarComp 𝐐 πP' πP).hom.app (R((f.left)_*⟦𝐐⟧).obj K) ≫
      L((πP')^*⟦𝐐⟧).map ((baseChangeMap 𝐐 sq₁).app K) ≫
        (baseChangeMap 𝐐 sq₂).app (L((πZ)^*⟦𝐐⟧).obj K) =
      (baseChangeMap 𝐐 sq).app K ≫
        R((f''.left)_*⟦𝐐⟧).map ((leftDerivedUpperStarComp 𝐐 πZ' πZ).hom.app K) := by
    intro K
    -- Unfold directly to avoid expensive rewrite matching through derived functor objects.
    unfold baseChangeMap
    exact_mod_proofs Adjunction.exchangeRight_app_paste
      (G₁ := L((πP)^*⟦𝐐⟧)) (G₁' := L((πZ)^*⟦𝐐⟧))
      (G₂ := L((πP')^*⟦𝐐⟧)) (G₂' := L((πZ')^*⟦𝐐⟧))
      (G := L((πP' ≫ πP)^*⟦𝐐⟧)) (G' := L((πZ' ≫ πZ)^*⟦𝐐⟧))
      (derivedUpperStarLowerStarAdjunction 𝐐 f.left)
      (derivedUpperStarLowerStarAdjunction 𝐐 f'.left)
      (derivedUpperStarLowerStarAdjunction 𝐐 f''.left)
      (pullbackSquareComparison 𝐐 sq₁) (pullbackSquareComparison 𝐐 sq₂)
      (pullbackSquareComparison 𝐐 sq) (leftDerivedUpperStarComp 𝐐 πP' πP)
      (leftDerivedUpperStarComp 𝐐 πZ' πZ) (pullbackSquareComparison_paste 𝐐 sq₁ sq₂ sq) K
  have h := liftExchange_paste_horiz_aux ℓ (baseChangeMap 𝐐 sq₁) (baseChangeMap 𝐐 sq₂)
    (baseChangeMap 𝐐 sq) hamb K
  unfold boundedConstructibleBaseChangeOfMap
  cast_proofs h

/-- The horizontal pasting law of the inverse proper base change isomorphisms, in the form of the
hypothesis of `CategoryTheory.Adjunction.exchangeRight_app_paste`. -/
lemma lowerStar_map_comp_inv_boundedConstructibleBaseChangeOfMap_app_paste [IsProper f.left]
    [IsProper f'.left] [IsProper f''.left] (sq₁ : IsPullback πZ f'.left f.left πP)
    (sq₂ : IsPullback πZ' f''.left f'.left πP')
    (sq : IsPullback (πZ' ≫ πZ) f''.left f.left (πP' ≫ πP)) (N : Dᵇc(Z.left)⟦𝐐⟧) :
    haveI := isIso_boundedConstructibleBaseChangeOfMap ℓ sq₁
    haveI := isIso_boundedConstructibleBaseChangeOfMap ℓ sq₂
    haveI := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
    (boundedConstructibleLowerStar ℓ f'').map
        ((boundedConstructibleUpperStarOfMapComp ℓ πZ πZ').hom.app N) ≫
      (asIso (boundedConstructibleBaseChangeOfMap ℓ sq₂.toCommSq)).symm.hom.app
        ((boundedConstructibleUpperStarOfMap ℓ πZ).obj N) ≫
      (boundedConstructibleUpperStarOfMap ℓ πP').map
        ((asIso (boundedConstructibleBaseChangeOfMap ℓ sq₁.toCommSq)).symm.hom.app N) =
    (asIso (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq)).symm.hom.app N ≫
      (boundedConstructibleUpperStarOfMapComp ℓ πP πP').hom.app
        ((boundedConstructibleLowerStar ℓ f).obj N) := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq₁
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq₂
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  have h := boundedConstructibleBaseChangeOfMap_app_paste ℓ sq₁.toCommSq sq₂.toCommSq
    sq.toCommSq N
  simp only [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
  rw [← cancel_epi ((boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq).app N),
    IsIso.hom_inv_id_assoc, ← reassoc_of% h, IsIso.hom_inv_id_assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Horizontal pasting of the base change maps of exceptional inverse images**: for two
horizontally pasted cartesian squares
```
Z'' --πZ'--> Z' --πZ--> Z
 |f''         |f'        |f
 v            v          v
P'' --πP'--> P' --πP--> P
```
of proper morphisms of schemes of finite type over fields `k₁`, `k₂`, `k₃`, the base change map
`γ : (πZ' ≫ πZ)^* Rf^! ⟶ Rf''^! (πP' ≫ πP)^*` of the outer square
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) is, through the composition isomorphisms of
the pullbacks, `πZ'^*` of the base change map `γ₁` of the right square followed by the base
change map `γ₂` of the left square at `πP^* K`. -/
theorem upperShriekBaseChangeOfMap_app_paste [IsProper f.left] [IsProper f'.left]
    [IsProper f''.left] (sq₁ : IsPullback πZ f'.left f.left πP)
    (sq₂ : IsPullback πZ' f''.left f'.left πP')
    (sq : IsPullback (πZ' ≫ πZ) f''.left f.left (πP' ≫ πP)) (K : Dᵇc(P.left)⟦𝐐⟧) :
    (boundedConstructibleUpperStarOfMapComp ℓ πZ πZ').hom.app
        ((boundedConstructibleUpperShriek ℓ f).obj K) ≫
      (boundedConstructibleUpperStarOfMap ℓ πZ').map ((upperShriekBaseChangeOfMap ℓ sq₁).app K) ≫
      (upperShriekBaseChangeOfMap ℓ sq₂).app ((boundedConstructibleUpperStarOfMap ℓ πP).obj K) =
    (upperShriekBaseChangeOfMap ℓ sq).app K ≫
      (boundedConstructibleUpperShriek ℓ f'').map
        ((boundedConstructibleUpperStarOfMapComp ℓ πP πP').hom.app K) := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq₁
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq₂
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  have key := Adjunction.exchangeRight_app_paste (lowerStarUpperShriekAdjunction ℓ f)
    (lowerStarUpperShriekAdjunction ℓ f') (lowerStarUpperShriekAdjunction ℓ f'')
    (asIso (boundedConstructibleBaseChangeOfMap ℓ sq₁.toCommSq)).symm
    (asIso (boundedConstructibleBaseChangeOfMap ℓ sq₂.toCommSq)).symm
    (asIso (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq)).symm
    (boundedConstructibleUpperStarOfMapComp ℓ πZ πZ')
    (boundedConstructibleUpperStarOfMapComp ℓ πP πP')
    (lowerStar_map_comp_inv_boundedConstructibleBaseChangeOfMap_app_paste ℓ sq₁ sq₂ sq) K
  rw [Adjunction.exchangeRight_eq_mateEquiv, Adjunction.exchangeRight_eq_mateEquiv,
    Adjunction.exchangeRight_eq_mateEquiv] at key
  exact key

/-- **Invertibility of the base change map of a horizontal composite**: if the base change maps
of the exceptional inverse images of the two squares are invertible at `K` and at `πP^* K`, so is
that of the outer square at `K`. -/
theorem isIso_upperShriekBaseChangeOfMap_app_paste [IsProper f.left] [IsProper f'.left]
    [IsProper f''.left] (sq₁ : IsPullback πZ f'.left f.left πP)
    (sq₂ : IsPullback πZ' f''.left f'.left πP')
    (sq : IsPullback (πZ' ≫ πZ) f''.left f.left (πP' ≫ πP)) (K : Dᵇc(P.left)⟦𝐐⟧)
    [IsIso ((upperShriekBaseChangeOfMap ℓ sq₁).app K)]
    [IsIso ((upperShriekBaseChangeOfMap ℓ sq₂).app
      ((boundedConstructibleUpperStarOfMap ℓ πP).obj K))] :
    IsIso ((upperShriekBaseChangeOfMap ℓ sq).app K) := by
  have h := upperShriekBaseChangeOfMap_app_paste ℓ sq₁ sq₂ sq K
  have : IsIso ((upperShriekBaseChangeOfMap ℓ sq).app K ≫
      (boundedConstructibleUpperShriek ℓ f'').map
        ((boundedConstructibleUpperStarOfMapComp ℓ πP πP').hom.app K)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((boundedConstructibleUpperShriek ℓ f'').map
    ((boundedConstructibleUpperStarOfMapComp ℓ πP πP').hom.app K))

end Paste
/-! ### Proper schemes over a point and field extensions -/

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {K₀ L : Type u} [Field K₀] [Field L]
  [Fact (ringChar K₀).Prime] [Fact (ringChar K₀ ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)] [Algebra K₀ L]
  {Z : Over (Spec (.of K₀))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Z' P' : Over (Spec (.of L))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ point K₀} {f' : Z' ⟶ P'} [IsProper f.left] [IsProper f'.left]
  {πZ : Z'.left ⟶ Z.left} {πP : P'.left ⟶ (point K₀).left}

omit [Fact (ringChar L).Prime] [Fact (ringChar L ≠ ℓ)] [Fact (ringChar K₀).Prime]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom] in
/-- A base `P'` over `L` whose structure morphism is an isomorphism is the base change of the
point `Spec K₀` along the field extension `L/K₀`. -/
lemma isPullback_of_isIso_hom [IsIso P'.hom] :
    IsPullback (P'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K₀ L))) P'.hom
      (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))) :=
  have : IsIso (point K₀).hom := inferInstanceAs (IsIso (𝟙 (Spec (.of K₀))))
  IsPullback.of_vert_isIso ⟨by simp⟩

omit [Algebra K₀ L] in
/-- **Pullback from a point commutes with internal homs**: for `πP : P' ⟶ Spec K₀`, the duality
map `πP^* RHom(A, N) ⟶ RHom(πP^* A, πP^* N)` with the identity as dualizing map is invertible,
every `A` on the point being dualizable (`ProEtale.CondensedRing.nonempty_hasLeftDual_point`). -/
theorem isIso_nearbyDualityMap_upperStarOfMap_id_of_point (N A : Dᵇc((point K₀).left)⟦𝐐⟧) :
    IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := point K₀) (Y := P') πP) A B)
      (𝟙 ((boundedConstructibleUpperStarOfMap ℓ (X := point K₀) (Y := P') πP).obj N)) A) := by
  obtain ⟨hA⟩ := nonempty_hasLeftDual_point ℓ (k := K₀) A
  rw [Verdier.nearbyDualityMap_id_eq_ihomComparison]
  exact Verdier.isIso_ihomComparison_app_of_exactPairing _ (ᘁA) A N

/-- **The base change map of `Ra^!` at the unit, for a proper scheme across a field extension**:
for a proper `K₀`-scheme `Z` with structure morphism `f`, its base change `f' : Z' ⟶ P'` along a
field extension `L/K₀` (`P' ≅ Spec L` over `L`), the base change map
`πZ^* Rf^! ℚ̄_ℓ ⟶ Rf'^! πP^* ℚ̄_ℓ` is invertible. It is the comparison of the dualizing complexes
of `Z` (`ProEtale.CondensedRing.dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap`),
up to those of the points, and these are invertible
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_fieldExtension`). -/
theorem isIso_upperShriekBaseChangeOfMap_app_unit_point
    (hP : IsPullback πP P'.hom (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))
    (sq : IsPullback πZ f'.left f.left πP) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sq).app (𝟙_ _)) := by
  have : IsProper P'.hom :=
    MorphismProperty.of_isPullback hP (inferInstanceAs (IsProper (𝟙 (Spec (.of K₀)))))
  have : IsProper (toPoint (point K₀)).left := by
    rw [toPoint_left]
    infer_instance
  have : IsProper (toPoint P').left := by
    rw [toPoint_left]
    infer_instance
  have hf : toPoint Z = f := toPoint_ext _ _
  have hf' : toPoint Z' = f' ≫ toPoint P' := (comp_toPoint f').symm
  have : IsProper (toPoint Z).left := by
    rw [hf]
    infer_instance
  have : IsProper (toPoint Z').left := by
    rw [toPoint_left, ← Over.w f']
    infer_instance
  let e := (Functor.Monoidal.εIso (boundedConstructibleUpperStarOfMap ℓ (X := point K₀)
    (Y := point L) (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))).inv
  have sqX : IsPullback πP (toPoint P').left (toPoint (point K₀)).left
      (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))) := by
    rw [toPoint_left, toPoint_left]
    exact hP
  have sqZ : IsPullback πZ (toPoint Z').left (toPoint Z).left
      (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))) := by
    rw [hf, hf', Over.comp_left, toPoint_left]
    exact sq.paste_vert hP
  have hX := isIso_dualizingComplexBaseChange_of_fieldExtension ℓ e (X := point K₀)
    (X' := P') sqX
  have hZ := isIso_dualizingComplexBaseChange_of_fieldExtension ℓ e (X := Z) (X' := Z') sqZ
  rw [dualizingComplexBaseChange_eq_comp_upperShriekBaseChangeOfMap ℓ e sqX sqZ sq] at hZ
  have := IsIso.of_isIso_comp_left ((boundedConstructibleUpperStarOfMap ℓ πZ).map
    (upperShriekDualizingComplexIso ℓ f).inv) ((upperShriekBaseChangeOfMap ℓ sq).app
    (dualizingComplex ℓ (point K₀)) ≫ (boundedConstructibleUpperShriek ℓ f').map
      (dualizingComplexBaseChange ℓ e sqX) ≫ (upperShriekDualizingComplexIso ℓ f').hom)
  have hω := IsIso.of_isIso_comp_right ((upperShriekBaseChangeOfMap ℓ sq).app
    (dualizingComplex ℓ (point K₀))) ((boundedConstructibleUpperShriek ℓ f').map
      (dualizingComplexBaseChange ℓ e sqX) ≫ (upperShriekDualizingComplexIso ℓ f').hom)
  /- Transport along `ω_s ≅ ℚ̄_ℓ`. -/
  let ι : dualizingComplex ℓ (point K₀) ≅ 𝟙_ _ := dualizingComplexPointIso ℓ K₀
  have hn := (upperShriekBaseChangeOfMap ℓ sq).naturality ι.hom
  have : IsIso ((boundedConstructibleUpperShriek ℓ f ⋙
      boundedConstructibleUpperStarOfMap ℓ πZ).map ι.hom ≫
        (upperShriekBaseChangeOfMap ℓ sq).app (𝟙_ _)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((boundedConstructibleUpperShriek ℓ f ⋙
    boundedConstructibleUpperStarOfMap ℓ πZ).map ι.hom) _

/-- **The two sides of the base change of `Ra^!` across a field extension are isomorphic**: for a
proper `K₀`-scheme `Z` with structure morphism `f` and its base change `f' : Z' ⟶ P'` along a field
extension `L/K₀`, every `N` on the point is dualizable, and so is `πP^* N`, so
`Rf^! N ≅ f^* N ⊗ Rf^! ℚ̄_ℓ`
(`ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_isDualizable`), whence
```
πZ^* Rf^! N ≅ πZ^* f^* N ⊗ πZ^* Rf^! ℚ̄_ℓ ≅ f'^* πP^* N ⊗ Rf'^! ℚ̄_ℓ ≅ Rf'^! πP^* N
```
through the base change map at the unit
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_unit_point`). -/
noncomputable def upperShriekBaseChangeIsoPoint
    (hP : IsPullback πP P'.hom (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))
    (sq : IsPullback πZ f'.left f.left πP) (N : Dᵇc((point K₀).left)⟦𝐐⟧) :
    (boundedConstructibleUpperStarOfMap ℓ πZ).obj ((boundedConstructibleUpperShriek ℓ f).obj N) ≅
      (boundedConstructibleUpperShriek ℓ f').obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := point K₀) (Y := P') πP).obj N) :=
  have := isIso_upperShriekUnitTensorMap_of_isDualizable ℓ f (isDualizable_point ℓ N)
  have := isIso_upperShriekUnitTensorMap_of_isDualizable ℓ f'
    ((isDualizable_point ℓ N).map
      (boundedConstructibleUpperStarOfMap ℓ (X := point K₀) (Y := P') πP))
  have := isIso_upperShriekBaseChangeOfMap_app_unit_point ℓ hP sq
  /- `πZ^* f^* N ≅ f'^* πP^* N`. -/
  let e₁ : (boundedConstructibleUpperStarOfMap ℓ (X := point K₀) (Y := Z') (πZ ≫ f.left)).obj N ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ).obj
        ((boundedConstructibleUpperStar _ ℓ f).obj N) :=
    ObjectProperty.isoMk _ ((leftDerivedUpperStarCompOfEq 𝐐
      (rfl : πZ ≫ f.left = πZ ≫ f.left)).app N.obj)
  let e₂ : (boundedConstructibleUpperStarOfMap ℓ (X := point K₀) (Y := Z') (πZ ≫ f.left)).obj N ≅
      (boundedConstructibleUpperStar _ ℓ f').obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := point K₀) (Y := P') πP).obj N) :=
    ObjectProperty.isoMk _ ((leftDerivedUpperStarCompOfEq 𝐐 sq.w.symm).app N.obj)
  let e := e₁.symm ≪≫ e₂
  /- `πZ^* Rf^! ℚ̄_ℓ ≅ Rf'^! ℚ̄_ℓ`. -/
  let t : (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ).obj
      ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _)) ≅
      (boundedConstructibleUpperShriek ℓ f').obj (𝟙_ _) :=
    asIso ((upperShriekBaseChangeOfMap ℓ sq).app (𝟙_ _)) ≪≫
      (boundedConstructibleUpperShriek ℓ f').mapIso
        (Functor.Monoidal.εIso (boundedConstructibleUpperStarOfMap ℓ (X := point K₀)
          (Y := P') πP)).symm
  (boundedConstructibleUpperStarOfMap ℓ πZ).mapIso (asIso (upperShriekUnitTensorMap ℓ f N)).symm ≪≫
    (Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ πZ) _ _).symm ≪≫
    tensorIso e t ≪≫
    asIso (upperShriekUnitTensorMap ℓ f'
      ((boundedConstructibleUpperStarOfMap ℓ (X := point K₀) (Y := P') πP).obj N))

/-- **Base change of `Ra^!` for a proper scheme across a field extension**: for a proper
`K₀`-scheme `Z` with structure morphism `f`, its base change `f' : Z' ⟶ P'` along a field
extension `L/K₀` (`P' ≅ Spec L` over `L`) and any `N` on the point, the base change map
`πZ^* Rf^! N ⟶ Rf'^! πP^* N` is invertible: `Rf'_*` of it is invertible since `πP^*` commutes with
internal homs out of the point
(`ProEtale.CondensedRing.isIso_lowerStar_map_upperShriekBaseChangeOfMap_app`), and both sides are
isomorphic (`ProEtale.CondensedRing.upperShriekBaseChangeIsoPoint`), so the endomorphism trick
applies (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_iso`). -/
theorem isIso_upperShriekBaseChangeOfMap_app_point
    (hP : IsPullback πP P'.hom (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))
    (sq : IsPullback πZ f'.left f.left πP) (N : Dᵇc((point K₀).left)⟦𝐐⟧) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sq).app N) :=
  have := isIso_lowerStar_map_upperShriekBaseChangeOfMap_app ℓ sq N
    (isIso_nearbyDualityMap_upperStarOfMap_id_of_point ℓ N _)
  isIso_upperShriekBaseChangeOfMap_app_of_iso ℓ sq N (upperShriekBaseChangeIsoPoint ℓ hP sq N)

/-- **Base change of `Ra^!` for a proper scheme across a field extension**, as an isomorphism of
functors `πZ^* Rf^! ≅ Rf'^! πP^*`. -/
theorem isIso_upperShriekBaseChangeOfMap_point
    (hP : IsPullback πP P'.hom (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))
    (sq : IsPullback πZ f'.left f.left πP) :
    IsIso (upperShriekBaseChangeOfMap ℓ sq) :=
  have := isIso_upperShriekBaseChangeOfMap_app_point ℓ hP sq
  NatIso.isIso_of_isIso_app _

end Point
/-! ### Projective morphisms along a generic point followed by a field extension -/

section GenericPoint

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ K₀ L : Type u} [Field k₁] [Field K₀] [Field L]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar K₀).Prime]
  [Fact (ringChar K₀ ≠ ℓ)] [Fact (ringChar L).Prime] [Fact (ringChar L ≠ ℓ)] [Algebra K₀ L]
  {Z Y P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z₀ Y₀ : Over (Spec (.of K₀))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
  [IsSeparated Z₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  {Z' P' : Over (Spec (.of L))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {i : Z ⟶ Y} {p : Y ⟶ P} [IsClosedImmersion i.left] [IsProper p.left]
  {i₀ : Z₀ ⟶ Y₀} {p₀ : Y₀ ⟶ point K₀} [IsClosedImmersion i₀.left] [IsProper p₀.left]
  {f' : Z' ⟶ P'} [IsProper f'.left]
  {η : Spec (.of K₀) ⟶ P.left} {πZ₀ : Z₀.left ⟶ Z.left} {πY₀ : Y₀.left ⟶ Y.left}
  {πZ' : Z'.left ⟶ Z₀.left} {πP : P'.left ⟶ (point K₀).left}

omit [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom] [IsProper f'.left]
  [Fact (ringChar L).Prime] [Fact (ringChar L ≠ ℓ)] [Algebra K₀ L] in
/-- **Base change of `Rb^!` for a projective morphism along a weakly étale map to a point**: let
`b = i ≫ p : Z ⟶ Y ⟶ P` be a closed immersion followed by a proper morphism `p` smooth of pure
relative dimension `d` (for instance the projection `P × ℙᴺ ⟶ P`), and let `η : Spec K₀ ⟶ P` be
weakly étale (for instance the inclusion of the generic point of an integral `P`, a localization),
with cartesian squares `πZ₀ ≫ i = i₀ ≫ πY₀` and `πY₀ ≫ p = p₀ ≫ η` over the point `Spec K₀`. Then
the base change map `πZ₀^* Rb^! ⟶ Rb₀^! η^*` is invertible
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale`,
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale` and the
composition law `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app`). -/
theorem isIso_upperShriekBaseChangeOfMap_app_of_projective_of_weaklyEtale (d : ℕ)
    [SmoothOfRelativeDimension d p.left] [WeaklyEtale η]
    (sqi : IsPullback πZ₀ i₀.left i.left πY₀) (sqp : IsPullback πY₀ p₀.left p.left η)
    (sqb : IsPullback πZ₀ (i₀ ≫ p₀).left (i ≫ p).left η) (K : Dᵇc(P.left)⟦𝐐⟧) :
    haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
    haveI : IsProper (i₀ ≫ p₀).left := inferInstanceAs (IsProper (i₀.left ≫ p₀.left))
    IsIso ((upperShriekBaseChangeOfMap ℓ sqb).app K) :=
  haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
  haveI : IsProper (i₀ ≫ p₀).left := inferInstanceAs (IsProper (i₀.left ≫ p₀.left))
  haveI : WeaklyEtale πY₀ := MorphismProperty.of_isPullback sqp.flip ‹WeaklyEtale η›
  haveI := isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale ℓ d sqp K
  isIso_upperShriekBaseChangeOfMap_comp_app_of_weaklyEtale ℓ sqi sqp sqb K

/-- **Base change of `Rb^!` for a projective morphism along a generic point followed by a field
extension**: let `b = i ≫ p : Z ⟶ Y ⟶ P` be a closed immersion followed by a proper morphism `p`
smooth of pure relative dimension `d` (`Z` projective over `P`), and let the base map
`g = πP ≫ η : P' ⟶ Spec K₀ ⟶ P` be a base change `πP : P' ≅ Spec L ⟶ Spec K₀` along a field
extension `L/K₀` followed by a weakly étale `η` (for instance the inclusion of the generic point
of an integral `P`, `K₀ = κ(P)`). Given the base change `b₀ = i₀ ≫ p₀ : Z₀ ⟶ Y₀ ⟶ Spec K₀` of `b`
along `η` and the base change `b' : Z' ⟶ P'` of `b₀` along `πP`, the base change map
`γ : (πZ' ≫ πZ₀)^* Rb^! ⟶ Rb'^! g^*` of the outer square is invertible.

The base change maps paste horizontally
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_paste`): along `η` this is
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_projective_of_weaklyEtale`, and
along the field extension of points it is
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_point`. -/
theorem isIso_upperShriekBaseChangeOfMap_app_of_projective_of_genericPoint (d : ℕ)
    [SmoothOfRelativeDimension d p.left] [WeaklyEtale η]
    (hP : IsPullback πP P'.hom (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))
    (sqi : IsPullback πZ₀ i₀.left i.left πY₀) (sqp : IsPullback πY₀ p₀.left p.left η)
    (sqb : IsPullback πZ₀ (i₀ ≫ p₀).left (i ≫ p).left η)
    (sq' : IsPullback πZ' f'.left (i₀ ≫ p₀).left πP)
    (sq : IsPullback (πZ' ≫ πZ₀) f'.left (i ≫ p).left (πP ≫ η)) (K : Dᵇc(P.left)⟦𝐐⟧) :
    haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
    IsIso ((upperShriekBaseChangeOfMap ℓ sq).app K) :=
  haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
  haveI : IsProper (i₀ ≫ p₀).left := inferInstanceAs (IsProper (i₀.left ≫ p₀.left))
  haveI := isIso_upperShriekBaseChangeOfMap_app_of_projective_of_weaklyEtale ℓ d sqi sqp sqb K
  haveI := isIso_upperShriekBaseChangeOfMap_app_point ℓ hP sq'
    ((boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := point K₀) η).obj K)
  isIso_upperShriekBaseChangeOfMap_app_paste ℓ sqb sq' sq K

/-- **Base change of `Rb^!` for a projective morphism along a generic point followed by a field
extension**, as an isomorphism of functors
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_projective_of_genericPoint`). -/
theorem isIso_upperShriekBaseChangeOfMap_of_projective_of_genericPoint (d : ℕ)
    [SmoothOfRelativeDimension d p.left] [WeaklyEtale η]
    (hP : IsPullback πP P'.hom (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))
    (sqi : IsPullback πZ₀ i₀.left i.left πY₀) (sqp : IsPullback πY₀ p₀.left p.left η)
    (sqb : IsPullback πZ₀ (i₀ ≫ p₀).left (i ≫ p).left η)
    (sq' : IsPullback πZ' f'.left (i₀ ≫ p₀).left πP)
    (sq : IsPullback (πZ' ≫ πZ₀) f'.left (i ≫ p).left (πP ≫ η)) :
    haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
    IsIso (upperShriekBaseChangeOfMap ℓ sq) :=
  haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
  haveI := isIso_upperShriekBaseChangeOfMap_app_of_projective_of_genericPoint ℓ d hP sqi sqp sqb
    sq' sq
  NatIso.isIso_of_isIso_app _

omit [Fact (ringChar K₀).Prime] [Fact (ringChar K₀ ≠ ℓ)] [Algebra K₀ L] in
/-- The invertibility of the base change map of the exceptional inverse image only depends on the
horizontal maps of the square up to equality. -/
lemma isIso_upperShriekBaseChangeOfMap_congr {f : Z ⟶ P} [IsProper f.left]
    {π₁ π₂ : Z'.left ⟶ Z.left} (h : π₁ = π₂) {g : P'.left ⟶ P.left}
    (sq₁ : IsPullback π₁ f'.left f.left g) (sq₂ : IsPullback π₂ f'.left f.left g) :
    IsIso (upperShriekBaseChangeOfMap ℓ sq₁) ↔ IsIso (upperShriekBaseChangeOfMap ℓ sq₂) := by
  subst h
  rfl

omit [IsClosedImmersion i₀.left] [IsProper p₀.left] in
/-- **Base change of `Rb^!` for a projective morphism along a generic point followed by a field
extension**, with the intermediate base change constructed: let `b = i ≫ p : Z ⟶ Y ⟶ P` be a
closed immersion followed by a proper morphism `p` smooth of pure relative dimension `d`, and
`g = πP ≫ η : P' ⟶ Spec K₀ ⟶ P` the base change `πP` of a field extension `L/K₀` (`P' ≅ Spec L`
over `L`, `ProEtale.CondensedRing.isPullback_of_isIso_hom`) followed by a weakly étale `η` (for
instance the inclusion of the generic point, `AlgebraicGeometry.affineLineGenericPoint` or
`Scheme.fromSpecFunctionField`). Then for every cartesian square `π ≫ b = b' ≫ g` with `b'`
proper, the base change map `π^* Rb^! ⟶ Rb'^! g^*` is an isomorphism.

The base change `Z₀ ⟶ Y₀ ⟶ Spec K₀` of `b` along `η` is formed by pullbacks, `Z'` is the base
change of `Z₀` along `πP` by the pasting law of pullbacks, and
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_projective_of_genericPoint`
applies. -/
theorem isIso_upperShriekBaseChangeOfMap_of_projective_of_comp_eq (d : ℕ)
    [SmoothOfRelativeDimension d p.left] (η : Spec (.of K₀) ⟶ P.left) [WeaklyEtale η]
    (hP : IsPullback πP P'.hom (point K₀).hom (Spec.map (CommRingCat.ofHom (algebraMap K₀ L))))
    {g : P'.left ⟶ P.left} (hg : πP ≫ η = g) {π : Z'.left ⟶ Z.left}
    (sq : IsPullback π f'.left (i ≫ p).left g) :
    haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
    IsIso (upperShriekBaseChangeOfMap ℓ sq) := by
  have : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
  subst hg
  /- The base change `Y₀ ⟶ Spec K₀` of `p` along `η`. -/
  let Y₀ : Over (Spec (.of K₀)) := Over.mk (pullback.snd p.left η)
  have : LocallyOfFiniteType Y₀.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : QuasiCompact Y₀.hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have : IsSeparated Y₀.hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  let p₀ : Y₀ ⟶ point K₀ := Over.homMk (pullback.snd p.left η) (Category.comp_id _)
  have : IsProper p₀.left := inferInstanceAs (IsProper (pullback.snd _ _))
  have : SmoothOfRelativeDimension d p₀.left :=
    inferInstanceAs (SmoothOfRelativeDimension d (pullback.snd _ _))
  /- The base change `Z₀ ⟶ Y₀` of `i` along `Y₀ ⟶ Y`. -/
  let Z₀ : Over (Spec (.of K₀)) := Over.mk (pullback.snd i.left (pullback.fst p.left η) ≫ Y₀.hom)
  have : LocallyOfFiniteType Z₀.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _ ≫ Y₀.hom))
  have : QuasiCompact Z₀.hom := inferInstanceAs (QuasiCompact (pullback.snd _ _ ≫ Y₀.hom))
  have : IsSeparated Z₀.hom := inferInstanceAs (IsSeparated (pullback.snd _ _ ≫ Y₀.hom))
  let i₀ : Z₀ ⟶ Y₀ := Over.homMk (pullback.snd i.left (pullback.fst p.left η)) rfl
  have : IsClosedImmersion i₀.left := inferInstanceAs (IsClosedImmersion (pullback.snd _ _))
  have : IsProper (i₀ ≫ p₀).left := inferInstanceAs (IsProper (i₀.left ≫ p₀.left))
  have sqi : IsPullback (pullback.fst i.left (pullback.fst p.left η)) i₀.left i.left
      (pullback.fst p.left η) := IsPullback.of_hasPullback _ _
  have sqp : IsPullback (pullback.fst p.left η) p₀.left p.left η := IsPullback.of_hasPullback _ _
  have sqb : IsPullback (pullback.fst i.left (pullback.fst p.left η)) (i₀ ≫ p₀).left
      (i ≫ p).left η := sqi.paste_vert sqp
  /- `Z'` is the base change of `Z₀` along `πP`. -/
  let πZ' : Z'.left ⟶ Z₀.left := sqb.lift π (f'.left ≫ πP) (by rw [sq.w, Category.assoc])
  have hπ : πZ' ≫ pullback.fst i.left (pullback.fst p.left η) = π := sqb.lift_fst _ _ _
  have sqo : IsPullback (πZ' ≫ pullback.fst i.left (pullback.fst p.left η)) f'.left (i ≫ p).left
      (πP ≫ η) := by
    rw [hπ]
    exact sq
  have sq' : IsPullback πZ' f'.left (i₀ ≫ p₀).left πP :=
    IsPullback.of_right sqo (sqb.lift_snd _ _ _) sqb
  rw [← isIso_upperShriekBaseChangeOfMap_congr ℓ hπ sqo sq]
  exact isIso_upperShriekBaseChangeOfMap_of_projective_of_genericPoint ℓ d hP sqi sqp sqb sq' sqo

omit [IsClosedImmersion i₀.left] [IsProper p₀.left] in
/-- **Base change of `Rb^!` for a projective morphism to a point over a generic point**:
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_of_projective_of_comp_eq` for a base `P'`
over `L` whose structure morphism is an isomorphism (for instance a slice of a point), and a base
map `g = P' ≅ Spec L ⟶ Spec K₀ ⟶[η] P` (`ProEtale.CondensedRing.isPullback_of_isIso_hom`). -/
theorem isIso_upperShriekBaseChangeOfMap_of_projective_of_isIso_hom (d : ℕ)
    [SmoothOfRelativeDimension d p.left] (η : Spec (.of K₀) ⟶ P.left) [WeaklyEtale η]
    [IsIso P'.hom] {g : P'.left ⟶ P.left}
    (hg : P'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K₀ L)) ≫ η = g)
    {π : Z'.left ⟶ Z.left} (sq : IsPullback π f'.left (i ≫ p).left g) :
    haveI : IsProper (i ≫ p).left := inferInstanceAs (IsProper (i.left ≫ p.left))
    IsIso (upperShriekBaseChangeOfMap ℓ sq) :=
  isIso_upperShriekBaseChangeOfMap_of_projective_of_comp_eq ℓ d η
    (isPullback_of_isIso_hom (P' := P')) ((Category.assoc _ _ _).trans hg) sq

end GenericPoint
end ProEtale.CondensedRing

/-! ### Generic points are weakly étale -/

section WeaklyEtale

/-- `Spec` of a localization `R ⟶ S⁻¹R` is weakly étale. -/
lemma weaklyEtale_SpecMap_algebraMap_of_isLocalization (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [WeaklyEtale.Spec_iff, CommRingCat.hom_ofHom, RingHom.weaklyEtale_algebraMap_iff]
  exact Algebra.WeaklyEtale.of_isLocalization R M S

variable (k : Type u) [Field k]

/-- The generic point `Spec k(x) ⟶ 𝔸¹_k` of the affine line, `k(x)` the fraction field of the
polynomial ring `k[x]`. -/
noncomputable def affineLineGenericPoint :
    Spec (.of (FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k))) ⟶
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (ULift.{u} (Fin 1)) k) _)) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).inv

/-- The generic point of the affine line is weakly étale: it is `Spec` of a localization. -/
instance weaklyEtale_affineLineGenericPoint : WeaklyEtale (affineLineGenericPoint k) := by
  have := weaklyEtale_SpecMap_algebraMap_of_isLocalization (MvPolynomial (ULift.{u} (Fin 1)) k)
    (FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k)) (nonZeroDivisors _)
  unfold affineLineGenericPoint
  infer_instance

variable {k} {K : Type u} [Field K] [Algebra k K] {x : K}

/-- An element `x` transcendental over `k` defines an injective evaluation `k[x] ⟶ K`. -/
lemma injective_aeval_of_transcendental (hx : Transcendental k x) :
    Function.Injective (MvPolynomial.aeval (R := k) fun _ : ULift.{u} (Fin 1) ↦ x) :=
  algebraicIndependent_iff_injective_aeval.mp
    ((algebraicIndependent_unique_type_iff (R := k) (x := fun _ : ULift.{u} (Fin 1) ↦ x)).mpr hx)

/-- For `x` transcendental over `k`, the embedding `k(x) ⟶ K` of the field of rational functions
in one variable sending the variable to `x`. -/
noncomputable def transcendentalFractionLift (hx : Transcendental k x) :
    FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k) →+* K :=
  IsFractionRing.lift (A := MvPolynomial (ULift.{u} (Fin 1)) k)
    (K := FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k))
    (g := (MvPolynomial.aeval (R := k) fun _ : ULift.{u} (Fin 1) ↦ x).toRingHom)
    (injective_aeval_of_transcendental hx)

/-- `k(x) ⟶ K` extends `MvPolynomial.aeval x : k[x] ⟶ K`. -/
lemma transcendentalFractionLift_comp_algebraMap (hx : Transcendental k x) :
    (transcendentalFractionLift hx).comp
        (algebraMap (MvPolynomial (ULift.{u} (Fin 1)) k)
          (FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k))) =
      (MvPolynomial.aeval (R := k) fun _ : ULift.{u} (Fin 1) ↦ x).toRingHom :=
  IsLocalization.lift_comp _

/-- **The slice point factors through the generic point of the line**: for `x` transcendental
over `k'`, the point `x : Spec K ⟶ 𝔸¹_{k'}` (`AlgebraicGeometry.traitSlicePoint`) is the field
extension `Spec K ⟶ Spec k'(x)` followed by the generic point `Spec k'(x) ⟶ 𝔸¹_{k'}`
(`AlgebraicGeometry.affineLineGenericPoint`), which is weakly étale. -/
lemma traitSlicePoint_eq_comp_affineLineGenericPoint (hx : Transcendental k x) :
    traitSlicePoint (k' := k) x =
      Spec.map (CommRingCat.ofHom (transcendentalFractionLift hx)) ≫ affineLineGenericPoint k := by
  rw [traitSlicePoint, affineLineGenericPoint, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    transcendentalFractionLift_comp_algebraMap]
  rfl
/-- **Transcendence over power series coefficients**: if `x` is transcendental over `k`, a
polynomial `q` over `k⟦t⟧` with `q(x) = 0` in `K⟦t⟧` (coefficients mapped coefficientwise) is zero:
the `n`-th coefficient of `q(x)` is `q_n(x)`, `q_n` the polynomial of the `n`-th coefficients. -/
lemma eq_zero_of_eval₂_map_C_eq_zero (hx : Transcendental k x) (q : Polynomial (PowerSeries k))
    (h : q.eval₂ (PowerSeries.map (algebraMap k K)) (PowerSeries.C x) = 0) : q = 0 := by
  ext j n
  rw [Polynomial.coeff_zero, map_zero]
  let qn : Polynomial k := ∑ i ∈ Finset.range (q.natDegree + 1),
    Polynomial.monomial i (PowerSeries.coeff n (q.coeff i))
  have hqn : Polynomial.aeval x qn = 0 := by
    have := congrArg (PowerSeries.coeff n) h
    rw [Polynomial.eval₂_eq_sum_range, map_sum, map_zero] at this
    rw [← this, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Polynomial.aeval_monomial, ← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_map]
  have hq : qn = 0 := by
    by_contra hne
    exact hx ⟨qn, hne, hqn⟩
  by_cases hj : j ≤ q.natDegree
  · have := congrArg (fun r ↦ Polynomial.coeff r j) hq
    simp only [qn, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_ite_eq'] at this
    simpa [Nat.lt_succ_of_le hj] using this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hj), map_zero]

/-- **The generic slice coordinate is transcendental**: if `x ∈ K` is transcendental over `k`, it
is transcendental over `Frac k⟦t⟧` in `Frac K⟦t⟧` (along `AlgebraicGeometry.traitFractionMap`):
clear the denominators of a polynomial relation
(`IsLocalization.integerNormalization_eval₂_eq_zero`) and compare coefficients of powers of `t`
(`AlgebraicGeometry.eq_zero_of_eval₂_map_C_eq_zero`). -/
lemma transcendental_traitGenericSliceCoord (hx : Transcendental k x) :
    letI := (traitFractionMap k K).toAlgebra
    Transcendental (FractionRing (PowerSeries k))
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.C x)) := by
  let := (traitFractionMap k K).toAlgebra
  rintro ⟨p, hp, hpx⟩
  have h := IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors (PowerSeries k))
    (traitFractionMap k K) p hpx
  rw [traitFractionMap_comp_algebraMap, ← Polynomial.hom_eval₂,
    _root_.map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  exact hp ((IsFractionRing.integerNormalization_eq_zero_iff (A := PowerSeries k)).mp
    (eq_zero_of_eval₂_map_C_eq_zero hx _ h))

/-- For `x ∈ K` transcendental over `k`, the embedding `Frac k⟦t⟧(x) ⟶ Frac K⟦t⟧` sending the
variable to `x`, over `AlgebraicGeometry.traitFractionMap`. -/
noncomputable def traitGenericSliceLift (hx : Transcendental k x) :
    FractionRing (MvPolynomial (ULift.{u} (Fin 1)) (FractionRing (PowerSeries k))) →+*
      FractionRing (PowerSeries K) :=
  letI := (traitFractionMap k K).toAlgebra
  transcendentalFractionLift (transcendental_traitGenericSliceCoord hx)

/-- `Frac k⟦t⟧(x) ⟶ Frac K⟦t⟧` extends the evaluation `Frac k⟦t⟧[x] ⟶ Frac K⟦t⟧` at `x`. -/
lemma traitGenericSliceLift_algebraMap (hx : Transcendental k x)
    (q : MvPolynomial (ULift.{u} (Fin 1)) (FractionRing (PowerSeries k))) :
    traitGenericSliceLift hx (algebraMap _ _ q) = MvPolynomial.eval₂ (traitFractionMap k K)
      (fun _ ↦ algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.C x)) q := by
  let := (traitFractionMap k K).toAlgebra
  exact RingHom.congr_fun (transcendentalFractionLift_comp_algebraMap
    (transcendental_traitGenericSliceCoord hx)) q

/-- **The generic slice factors through the generic point of the line**: for `x` transcendental
over `k`, the generic slice over the generic point `σ_η : Spec Frac K⟦t⟧ ⟶ 𝔸¹_η`
(`AlgebraicGeometry.traitGenericSlice`, `η = Spec Frac k⟦t⟧`) is the field extension
`Spec Frac K⟦t⟧ ⟶ Spec Frac k⟦t⟧(x)` (`AlgebraicGeometry.traitGenericSliceLift`) followed by the
generic point `Spec Frac k⟦t⟧(x) ⟶ 𝔸¹_η` (`AlgebraicGeometry.affineLineGenericPoint`), which is
weakly étale. -/
lemma traitGenericSlice_eq_comp_affineLineGenericPoint (hx : Transcendental k x) :
    traitGenericSlice (k' := k) x =
      Spec.map (CommRingCat.ofHom (traitGenericSliceLift hx)) ≫
        affineLineGenericPoint (FractionRing (PowerSeries k)) := by
  apply (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (traitGenericSpec k)).hom_ext
  · rw [traitGenericSlice_map, Category.assoc, affineLineGenericPoint, Category.assoc]
    unfold traitGenericSpec
    rw [AffineSpace.map_SpecMap, Iso.inv_hom_id_assoc, traitSlice, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    refine congrArg (fun φ : MvPolynomial (ULift.{u} (Fin 1)) (PowerSeries k) →+*
      FractionRing (PowerSeries K) ↦ Spec.map (CommRingCat.ofHom φ) ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k))).inv) ?_
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, CommRingCat.hom_ofHom,
        MvPolynomial.map_C, traitGenericSliceLift_algebraMap, MvPolynomial.eval₂_C,
        traitSliceRingHom, MvPolynomial.eval₂Hom_C, ← RingHom.comp_apply]
      exact (RingHom.congr_fun (traitFractionMap_comp_algebraMap k K) a).symm
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, CommRingCat.hom_ofHom,
        MvPolynomial.map_X, traitGenericSliceLift_algebraMap, MvPolynomial.eval₂_X,
        traitSliceRingHom, MvPolynomial.eval₂Hom_X']
  · rw [traitGenericSlice_over, Category.assoc, affineLineGenericPoint, Category.assoc,
      AffineSpace.SpecIso_inv_over, traitGenericSpecMap, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    refine congrArg (fun φ : FractionRing (PowerSeries k) →+* FractionRing (PowerSeries K) ↦
      Spec.map (CommRingCat.ofHom φ)) ?_
    refine RingHom.ext fun a ↦ ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, traitGenericSliceLift_algebraMap,
      MvPolynomial.eval₂_C]

end WeaklyEtale

end AlgebraicGeometry
