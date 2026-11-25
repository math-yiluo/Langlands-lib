/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsRegular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.FiberRank

/-!
# Descending a locally free module along a change of coefficients, from transition matrices

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, `S` a scheme and `L` a module
object over `Λ'_S`. Suppose given a finite pro-étale cover `{f_k : V_k ⟶ S}` with trivialisations
`e_k : Λ'_{V_k}^{n_k} ≅ f_k^* L`. On the fibre products `P_{jk} = V_j ×_S V_k` they differ by the
*transition isomorphisms* `p₁^* Λ'^{n_j} ≅ p₂^* Λ'^{n_k}`
(`ProEtale.CondensedRing.finiteFreeTransition`). If all transition isomorphisms and their
inverses have their matrix entries in the image of `Γ(Λ_{P_{jk}}) ⟶ Γ(Λ'_{P_{jk}})`
(`ProEtale.CondensedRing.IsDefinedOver`), and the units `Λ_{V_k}^{n_k} ⟶ Res(Λ'_{V_k}^{n_k})`
are monomorphisms, then `L ≅ Λ'_S ⊗_{Λ_S} L'` for a locally free `Λ_S`-module `L'`
(`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver`).

The lattices `σ_k : Λ_{V_k}^{n_k} ⟶ f_k^* Res L` spanned by the bases `e_k` agree on the fibre
products up to the matrices over `Λ`, so their cokernels glue
(`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_cover`). The comparison of
`Λ_P^n` with `Λ'_P^n` through the pullbacks rests on the compatibility of (Pull) with the free
module of rank one (`ProEtale.CondensedRing.pullIso_hom_app_regular_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- If `x₁ ≫ κ = k ≫ x₂` for isomorphisms `κ` and `k`, then `x₂ ≫ κ⁻¹ = k⁻¹ ≫ x₁`. -/
lemma comp_inv_eq_inv_comp_of_comp_hom_eq {C : Type*} [Category* C] {A B X Y : C} {x₁ : A ⟶ B}
    {x₂ : X ⟶ Y} (κ : B ≅ Y) (k : A ≅ X) (h : x₁ ≫ κ.hom = k.hom ≫ x₂) :
    x₂ ≫ κ.inv = k.inv ≫ x₁ := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- The composite `e₁ ≪≫ κ ≪≫ e₂` of isomorphisms intertwines `e₁` and `e₂⁻¹` with `κ`. -/
lemma hom_comp_eq_trans_hom_comp {C : Type*} [Category* C] {X Y Z W : C} (e₁ : X ≅ Y)
    (κ : Y ≅ Z) (e₂ : Z ≅ W) : e₁.hom ≫ κ.hom = (e₁ ≪≫ κ ≪≫ e₂).hom ≫ e₂.inv := by
  simp

/-- The inverse of the composite `e₁ ≪≫ κ ≪≫ e₂` intertwines `e₂⁻¹` and `e₁` with `κ⁻¹`. -/
lemma inv_comp_eq_trans_inv_comp {C : Type*} [Category* C] {X Y Z W : C} (e₁ : X ≅ Y)
    (κ : Y ≅ Z) (e₂ : Z ≅ W) : e₂.inv ≫ κ.inv = (e₁ ≪≫ κ ≪≫ e₂).inv ≫ e₁.hom := by
  simp

namespace Limits

/-- Let `π₁` and `π₂` be cokernels of `x : A ⟶ N₁` and `y : B ⟶ N₂`, and `e : N₁ ≅ N₂` an
isomorphism such that `x ≫ e` factors through `y` and `y ≫ e⁻¹` factors through `x`. Then the
cokernels are isomorphic compatibly with `e`. -/
lemma exists_iso_comp_eq_of_isColimit_cokernelCofork_of_factors {C : Type*} [Category* C]
    [Preadditive C] {A B N₁ N₂ Q₁ Q₂ : C} {x : A ⟶ N₁} {y : B ⟶ N₂} {π₁ : N₁ ⟶ Q₁}
    {π₂ : N₂ ⟶ Q₂} {w₁ : x ≫ π₁ = 0 ≫ π₁} {w₂ : y ≫ π₂ = 0 ≫ π₂}
    (h₁ : IsColimit (Cofork.ofπ π₁ w₁)) (h₂ : IsColimit (Cofork.ofπ π₂ w₂)) (e : N₁ ≅ N₂)
    (c₁ : A ⟶ B) (hc₁ : x ≫ e.hom = c₁ ≫ y) (c₂ : B ⟶ A) (hc₂ : y ≫ e.inv = c₂ ≫ x) :
    ∃ ψ : Q₁ ≅ Q₂, π₁ ≫ ψ.hom = e.hom ≫ π₂ := by
  have w₁' : x ≫ π₁ = 0 := by rw [w₁, zero_comp]
  have w₂' : y ≫ π₂ = 0 := by rw [w₂, zero_comp]
  obtain ⟨u, hu⟩ := Cofork.IsColimit.desc' h₁ (e.hom ≫ π₂)
    (by rw [reassoc_of% hc₁, w₂', comp_zero, zero_comp])
  obtain ⟨v, hv⟩ := Cofork.IsColimit.desc' h₂ (e.inv ≫ π₁)
    (by rw [reassoc_of% hc₂, w₁', comp_zero, zero_comp])
  change π₁ ≫ u = _ at hu
  change π₂ ≫ v = _ at hv
  refine ⟨⟨u, v, Cofork.IsColimit.hom_ext h₁ ?_, Cofork.IsColimit.hom_ext h₂ ?_⟩, hu⟩
  · change π₁ ≫ u ≫ v = π₁ ≫ 𝟙 _
    rw [reassoc_of% hu, hv, e.hom_inv_id_assoc, Category.comp_id]
  · change π₂ ≫ v ≫ u = π₂ ≫ 𝟙 _
    rw [reassoc_of% hv, hu, e.inv_hom_id_assoc, Category.comp_id]

end Limits

namespace Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {D : Type*} [Category* D] [MonoidalCategory D] [Abelian D] [MonoidalPreadditive D]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]
  {S : D} [MonObj S] [PreservesFiniteColimits (tensorLeft S)]
  (F : Mod C R ⥤ Mod D S) [F.Additive] (e : F.obj (regular R) ≅ regular S)

omit [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)] in
/-- The identification `F(R^n) ≅ S^n` on the summands. -/
@[reassoc (attr := simp)]
lemma ι_comp_finiteFreeIsoMap_inv (n : ℕ) (i : Fin n) :
    biproduct.ι (fun _ : Fin n ↦ regular S) i ≫ (finiteFreeIsoMap F e n).inv =
      e.inv ≫ F.map (biproduct.ι (fun _ : Fin n ↦ regular R) i) := by
  simp [finiteFreeIsoMap]

omit [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)] in
/-- The identification `F(R^n) ≅ S^n` on the summands. -/
@[reassoc (attr := simp)]
lemma map_ι_comp_finiteFreeIsoMap_hom (n : ℕ) (i : Fin n) :
    F.map (biproduct.ι (fun _ : Fin n ↦ regular R) i) ≫ (finiteFreeIsoMap F e n).hom =
      e.hom ≫ biproduct.ι (fun _ : Fin n ↦ regular S) i := by
  rw [← cancel_mono (finiteFreeIsoMap F e n).inv, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Category.assoc, ι_comp_finiteFreeIsoMap_inv, Iso.hom_inv_id_assoc]

omit [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)] in
/-- The identification `F(R^n) ≅ S^n` on the projections. -/
@[reassoc (attr := simp)]
lemma finiteFreeIsoMap_hom_comp_π (n : ℕ) (i : Fin n) :
    (finiteFreeIsoMap F e n).hom ≫ biproduct.π (fun _ : Fin n ↦ regular S) i =
      F.map (biproduct.π (fun _ : Fin n ↦ regular R) i) ≫ e.hom := by
  simp [finiteFreeIsoMap]

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-! ### Compatibility of `comapUpperStarIso` with the comparison of a commutative square -/

section Square

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The commutation of restriction of scalars with the pullbacks is compatible with the
transport along an equality of morphisms. -/
@[reassoc]
lemma comapUpperStarIso_hom_app_upperStarCongr {Z T : Scheme.{u}} {h h' : Z ⟶ T} (eq : h = h')
    (K : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ' T)) :
    (comapUpperStarIso a h).hom.app K ≫
        (upperStarCongr Λ eq).hom.app ((Mod.comap (coefficientMap a T)).obj K) =
      (Mod.comap (coefficientMap a Z)).map ((upperStarCongr Λ' eq).hom.app K) ≫
        (comapUpperStarIso a h').hom.app K := by
  subst eq
  simp [upperStarCongr_hom_app_eq_eqToHom]

/-- **The commutation of restriction of scalars with the pullbacks is compatible with the
comparison of a commutative square** `g' ≫ f = f' ≫ g`: through `Res ⋙ f'^* g^* ≅ f'^* g^* Res`
and `Res ⋙ g'^* f^* ≅ g'^* f^* Res`, the comparisons `f'^* g^* ≅ g'^* f^*` over `Λ'` and `Λ`
agree. -/
lemma comapUpperStarIso_comp_upperStarSquareComparison (sq : CommSq g' f' f g)
    (L : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    (comapUpperStarIso a f').hom.app ((g)^*⟦Λ'⟧.obj L) ≫
        (f')^*⟦Λ⟧.map ((comapUpperStarIso a g).hom.app L) ≫
        (upperStarSquareComparison Λ sq).hom.app ((Mod.comap (coefficientMap a Y)).obj L) =
      (Mod.comap (coefficientMap a X')).map ((upperStarSquareComparison Λ' sq).hom.app L) ≫
        (comapUpperStarIso a g').hom.app ((f)^*⟦Λ'⟧.obj L) ≫
        (g')^*⟦Λ⟧.map ((comapUpperStarIso a f).hom.app L) := by
  have h₁ := squareCompatible_upperStarComp a f' g L
  have h₂ := squareCompatible_upperStarComp a g' f L
  simp only [Functor.pasteSquareIso_hom_app] at h₁ h₂
  have h₁' : (comapUpperStarIso a f').hom.app ((g)^*⟦Λ'⟧.obj L) ≫
      (f')^*⟦Λ⟧.map ((comapUpperStarIso a g).hom.app L) =
      (Mod.comap (coefficientMap a X')).map ((upperStarComp Λ' f' g).inv.app L) ≫
        (comapUpperStarIso a (f' ≫ g)).hom.app L ≫
        (upperStarComp Λ f' g).hom.app ((Mod.comap (coefficientMap a Y)).obj L) := by
    rw [← h₁, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [reassoc_of% h₁', upperStarSquareComparison_hom_app, upperStarSquareComparison_hom_app,
    Iso.hom_inv_id_app_assoc, comapUpperStarIso_hom_app_upperStarCongr_assoc, ← h₂,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]

end Square

/-! ### Free modules, extension of scalars and pullbacks -/

section FiniteFree

/-- The extension of scalars along `a_X : Λ_X ⟶ Λ'_X` sends `Λ_X^n` to `Λ'_X^n`. -/
noncomputable abbrev extendScalarsFiniteFreeIso (X : Scheme.{u}) (n : ℕ) :
    (Mod.extendScalars (coefficientMap a X)).obj (Mod.finiteFree (condensedRingObj Λ X) n) ≅
      Mod.finiteFree (condensedRingObj Λ' X) n :=
  Mod.finiteFreeIsoMap _ (Mod.extendScalarsObjRegularIso (coefficientMap a X)) n

/-- (Pull) on `Λ_Y^n` is compatible with the identifications `f^* Λ_Y^n ≅ Λ_X^n` and
`Λ' ⊗_Λ Λ^n ≅ Λ'^n`. -/
lemma pullIso_hom_app_finiteFree_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (pullIso a f).hom.app (Mod.finiteFree (condensedRingObj Λ Y) n) ≫
        (f)^*⟦Λ'⟧.map (extendScalarsFiniteFreeIso a Y n).hom ≫
        (upperStarFiniteFreeIso Λ' f n).hom =
      (Mod.extendScalars (coefficientMap a X)).map (upperStarFiniteFreeIso Λ f n).hom ≫
        (extendScalarsFiniteFreeIso a X n).hom := by
  refine Functor.map_biproduct_hom_ext ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X))
    fun i ↦ ?_
  have hn := (pullIso a f).hom.naturality
    (biproduct.ι (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ Y)) i)
  simp only [Functor.comp_map, upperStarFiniteFreeIso] at hn ⊢
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, Mod.map_ι_comp_finiteFreeIsoMap_hom,
    Functor.map_comp_assoc, Mod.map_ι_comp_finiteFreeIsoMap_hom, ← Functor.map_comp_assoc,
    Mod.map_ι_comp_finiteFreeIsoMap_hom, Functor.map_comp_assoc,
    Mod.map_ι_comp_finiteFreeIsoMap_hom, reassoc_of% (pullIso_hom_app_regular_comp a f)]

/-- A morphism `Y : p^* Λ'_V^n ⟶ p'^* Λ'_{V'}^m` over `P` is *defined over `Λ`* if, through the
identifications `p^* Λ'_V ≅ Λ'_P ≅ p'^* Λ'_{V'}`, its matrix entries are multiplications by
global sections of `Λ'_P` coming from global sections of `Λ_P`. -/
def IsDefinedOver {P V V' : Scheme.{u}} (p : P ⟶ V) (p' : P ⟶ V') {n m : ℕ}
    (Y : (p)^*⟦Λ'⟧.obj (Mod.finiteFree (condensedRingObj Λ' V) n) ⟶
      (p')^*⟦Λ'⟧.obj (Mod.finiteFree (condensedRingObj Λ' V') m)) : Prop :=
  ∀ i j, ∃ t : Γ (condensedRingObj Λ P),
    (upperStarObjRegularIso Λ' p).inv ≫
        (p)^*⟦Λ'⟧.map (biproduct.ι (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ' V)) i) ≫ Y ≫
        (p')^*⟦Λ'⟧.map (biproduct.π (fun _ : Fin m ↦ Mod.regular (condensedRingObj Λ' V')) j) ≫
        (upperStarObjRegularIso Λ' p').hom =
      (Mod.regularEndRingHom (Γ.map (coefficientMap a P) t)).asHom

/-- **Descent of a morphism defined over `Λ`**: a morphism `Y : p^* Λ'_V^n ⟶ p'^* Λ'_{V'}^m`
defined over `Λ` is, through (Pull), the extension of scalars of a morphism
`p^* Λ_V^n ⟶ p'^* Λ_{V'}^m`. -/
lemma exists_extendScalars_map_eq_of_isDefinedOver {P V V' : Scheme.{u}} (p : P ⟶ V)
    (p' : P ⟶ V') {n m : ℕ}
    (Y : (p)^*⟦Λ'⟧.obj (Mod.finiteFree (condensedRingObj Λ' V) n) ⟶
      (p')^*⟦Λ'⟧.obj (Mod.finiteFree (condensedRingObj Λ' V') m))
    (hY : IsDefinedOver a p p' Y) :
    ∃ c₁ : (p)^*⟦Λ⟧.obj (Mod.finiteFree (condensedRingObj Λ V) n) ⟶
        (p')^*⟦Λ⟧.obj (Mod.finiteFree (condensedRingObj Λ V') m),
      (Mod.extendScalars (coefficientMap a P)).map c₁ ≫
          (pullIso a p').hom.app (Mod.finiteFree (condensedRingObj Λ V') m) ≫
          (p')^*⟦Λ'⟧.map (extendScalarsFiniteFreeIso a V' m).hom =
        (pullIso a p).hom.app (Mod.finiteFree (condensedRingObj Λ V) n) ≫
          (p)^*⟦Λ'⟧.map (extendScalarsFiniteFreeIso a V n).hom ≫ Y := by
  choose t ht using hY
  let M : Mod.finiteFree (condensedRingObj Λ P) n ⟶ Mod.finiteFree (condensedRingObj Λ P) m :=
    biproduct.matrix fun i j ↦ (Mod.regularEndRingHom (t i j)).asHom
  refine ⟨(upperStarFiniteFreeIso Λ p n).hom ≫ M ≫ (upperStarFiniteFreeIso Λ p' m).inv, ?_⟩
  have h₁ := pullIso_hom_app_finiteFree_comp a p n
  have h₂ := pullIso_hom_app_finiteFree_comp a p' m
  -- the matrix of `Y` in the bases of `Λ'_P^n` and `Λ'_P^m`
  have hM : (Mod.extendScalars (coefficientMap a P)).map M ≫
      (extendScalarsFiniteFreeIso a P m).hom =
      (extendScalarsFiniteFreeIso a P n).hom ≫ (upperStarFiniteFreeIso Λ' p n).inv ≫ Y ≫
        (upperStarFiniteFreeIso Λ' p' m).hom := by
    refine Functor.map_biproduct_hom_ext (Mod.extendScalars (coefficientMap a P)) fun i ↦
      biproduct.hom_ext _ _ fun j ↦ ?_
    simp only [upperStarFiniteFreeIso, Category.assoc, Mod.finiteFreeIsoMap_hom_comp_π,
      Mod.map_ι_comp_finiteFreeIsoMap_hom_assoc, Mod.ι_comp_finiteFreeIsoMap_inv_assoc]
    have hc : biproduct.ι (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ P)) i ≫ M ≫
        biproduct.π (fun _ : Fin m ↦ Mod.regular (condensedRingObj Λ P)) j =
        (Mod.regularEndRingHom (t i j)).asHom := by
      simp [M]
    have hc' : (Mod.extendScalars (coefficientMap a P)).map
          (biproduct.ι (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ P)) i) ≫
        (Mod.extendScalars (coefficientMap a P)).map M ≫
        (Mod.extendScalars (coefficientMap a P)).map
          (biproduct.π (fun _ : Fin m ↦ Mod.regular (condensedRingObj Λ P)) j) =
        (Mod.extendScalars (coefficientMap a P)).map (Mod.regularEndRingHom (t i j)).asHom := by
      rw [← hc, Functor.map_comp, Functor.map_comp]
    have key := Mod.extendScalarsObjRegularIso_inv_comp_map (coefficientMap a P) (t i j)
    rw [ht i j, ← Iso.inv_comp_eq, reassoc_of% hc', reassoc_of% key, Iso.inv_hom_id,
      Category.comp_id]
  rw [← cancel_mono (upperStarFiniteFreeIso Λ' p' m).hom]
  simp only [Functor.map_comp, Category.assoc]
  have hβ : (Mod.extendScalars (coefficientMap a P)).map (upperStarFiniteFreeIso Λ p' m).inv ≫
      (Mod.extendScalars (coefficientMap a P)).map (upperStarFiniteFreeIso Λ p' m).hom ≫
      (extendScalarsFiniteFreeIso a P m).hom = (extendScalarsFiniteFreeIso a P m).hom := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h₂, hβ, hM, ← reassoc_of% h₁, Iso.hom_inv_id_assoc]

end FiniteFree

/-! ### Gluing the lattices spanned by the bases -/

section Glue

/-- The transition isomorphism `p₁^* Λ'_V^n ≅ p₂^* Λ'_W^m` between two trivialisations
`e : Λ'_V^n ≅ f^* L` and `e' : Λ'_W^m ≅ g^* L` over a cartesian square `p₁ ≫ f = p₂ ≫ g`. -/
noncomputable def finiteFreeTransition {S V W P : Scheme.{u}} {f : V ⟶ S} {g : W ⟶ S}
    {p₁ : P ⟶ V} {p₂ : P ⟶ W} (h : IsPullback p₁ p₂ f g)
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)} {n m : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ (f)^*⟦Λ'⟧.obj L)
    (e' : Mod.finiteFree (condensedRingObj Λ' W) m ≅ (g)^*⟦Λ'⟧.obj L) :
    (p₁)^*⟦Λ'⟧.obj (Mod.finiteFree (condensedRingObj Λ' V) n) ≅
      (p₂)^*⟦Λ'⟧.obj (Mod.finiteFree (condensedRingObj Λ' W) m) :=
  (p₁)^*⟦Λ'⟧.mapIso e ≪≫ (upperStarSquareComparison Λ' h.flip.toCommSq).app L ≪≫
    (p₂)^*⟦Λ'⟧.mapIso e'.symm

/-- The lattice `Λ_V^n ⟶ Res(f^* L)` spanned by a basis `e : Λ'_V^n ≅ f^* L`: the adjoint of
`Λ' ⊗_Λ Λ^n ≅ Λ'^n ≅ f^* L`. -/
noncomputable def finiteFreeLattice {V : Scheme.{u}}
    {N : Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ' V)} {n : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ N) :
    Mod.finiteFree (condensedRingObj Λ V) n ⟶ (Mod.comap (coefficientMap a V)).obj N :=
  (Mod.extendRestrictAdjunction (coefficientMap a V)).homEquiv _ _
    ((extendScalarsFiniteFreeIso a V n).hom ≫ e.hom)

/-- The adjoint of the pullback of a lattice, through (Pull). -/
lemma homEquiv_symm_upperStar_map_finiteFreeLattice {V P : Scheme.{u}} (p : P ⟶ V)
    {N : Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ' V)} {n : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ N) :
    ((Mod.extendRestrictAdjunction (coefficientMap a P)).homEquiv _ _).symm
        ((p)^*⟦Λ⟧.map (finiteFreeLattice a e) ≫ (comapUpperStarIso a p).inv.app N) =
      (pullIso a p).hom.app _ ≫ (p)^*⟦Λ'⟧.map ((extendScalarsFiniteFreeIso a V n).hom ≫ e.hom) := by
  rw [← pullIso_hom_app_comp_upperStar_map_homEquiv_symm, finiteFreeLattice, Equiv.symm_apply_apply]

/-- Let `κ : p₁^* f^* ≅ p₂^* g^*` and `κ'` be comparisons over `Λ` and `Λ'`, compatible with the
restriction of scalars, and `e, e'` bases of `f^* L` and `g^* L` whose transition
`T : p₁^* Λ'^n ⟶ p₂^* Λ'^m` through `κ'` is defined over `Λ`. Then the pullback of the lattice
of `e`, followed by `κ`, factors through the pullback of the lattice of `e'`. -/
lemma exists_comp_eq_upperStar_map_finiteFreeLattice {S V W P : Scheme.{u}} {f : V ⟶ S}
    {g : W ⟶ S} (p₁ : P ⟶ V) (p₂ : P ⟶ W)
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)}
    (κ : (f)^*⟦Λ⟧ ⋙ (p₁)^*⟦Λ⟧ ≅ (g)^*⟦Λ⟧ ⋙ (p₂)^*⟦Λ⟧)
    (κ' : (f)^*⟦Λ'⟧ ⋙ (p₁)^*⟦Λ'⟧ ≅ (g)^*⟦Λ'⟧ ⋙ (p₂)^*⟦Λ'⟧)
    (hκ : (comapUpperStarIso a p₁).hom.app ((f)^*⟦Λ'⟧.obj L) ≫
        (p₁)^*⟦Λ⟧.map ((comapUpperStarIso a f).hom.app L) ≫
        κ.hom.app ((Mod.comap (coefficientMap a S)).obj L) =
      (Mod.comap (coefficientMap a P)).map (κ'.hom.app L) ≫
        (comapUpperStarIso a p₂).hom.app ((g)^*⟦Λ'⟧.obj L) ≫
        (p₂)^*⟦Λ⟧.map ((comapUpperStarIso a g).hom.app L))
    {n m : ℕ} (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ (f)^*⟦Λ'⟧.obj L)
    (e' : Mod.finiteFree (condensedRingObj Λ' W) m ≅ (g)^*⟦Λ'⟧.obj L)
    (T : (p₁)^*⟦Λ'⟧.obj (Mod.finiteFree (condensedRingObj Λ' V) n) ⟶
      (p₂)^*⟦Λ'⟧.obj (Mod.finiteFree (condensedRingObj Λ' W) m))
    (hTe : (p₁)^*⟦Λ'⟧.map e.hom ≫ κ'.hom.app L = T ≫ (p₂)^*⟦Λ'⟧.map e'.hom)
    (hT : IsDefinedOver a p₁ p₂ T) :
    ∃ c₁ : (p₁)^*⟦Λ⟧.obj (Mod.finiteFree (condensedRingObj Λ V) n) ⟶
        (p₂)^*⟦Λ⟧.obj (Mod.finiteFree (condensedRingObj Λ W) m),
      (p₁)^*⟦Λ⟧.map (finiteFreeLattice a e ≫ (comapUpperStarIso a f).hom.app L) ≫
          κ.hom.app ((Mod.comap (coefficientMap a S)).obj L) =
        c₁ ≫ (p₂)^*⟦Λ⟧.map (finiteFreeLattice a e' ≫ (comapUpperStarIso a g).hom.app L) := by
  obtain ⟨c₁, hc₁⟩ := exists_extendScalars_map_eq_of_isDefinedOver a p₁ p₂ _ hT
  refine ⟨c₁, ?_⟩
  -- compare after the isomorphism `θ` into the restriction of scalars of `p₂^* g^* L`
  let θ := (p₂)^*⟦Λ⟧.map ((comapUpperStarIso a g).inv.app L) ≫
    (comapUpperStarIso a p₂).inv.app ((g)^*⟦Λ'⟧.obj L)
  rw [← cancel_mono θ]
  apply ((Mod.extendRestrictAdjunction (coefficientMap a P)).homEquiv _ _).symm.injective
  have hx : ((p₁)^*⟦Λ⟧.map (finiteFreeLattice a e ≫ (comapUpperStarIso a f).hom.app L) ≫
      κ.hom.app ((Mod.comap (coefficientMap a S)).obj L)) ≫ θ =
      ((p₁)^*⟦Λ⟧.map (finiteFreeLattice a e) ≫ (comapUpperStarIso a p₁).inv.app _) ≫
        (Mod.comap (coefficientMap a P)).map (κ'.hom.app L) := by
    have hinner : (p₁)^*⟦Λ⟧.map ((comapUpperStarIso a f).hom.app L) ≫
        κ.hom.app ((Mod.comap (coefficientMap a S)).obj L) ≫
        (p₂)^*⟦Λ⟧.map ((comapUpperStarIso a g).inv.app L) ≫
        (comapUpperStarIso a p₂).inv.app ((g)^*⟦Λ'⟧.obj L) =
        (comapUpperStarIso a p₁).inv.app ((f)^*⟦Λ'⟧.obj L) ≫
          (Mod.comap (coefficientMap a P)).map (κ'.hom.app L) := by
      rw [← cancel_epi ((comapUpperStarIso a p₁).hom.app ((f)^*⟦Λ'⟧.obj L)),
        Iso.hom_inv_id_app_assoc, reassoc_of% hκ, ← Functor.map_comp_assoc,
        Iso.hom_inv_id_app]
      simp
    simp only [θ, Functor.map_comp, Category.assoc]
    rw [hinner]
  have hy : (p₂)^*⟦Λ⟧.map (finiteFreeLattice a e' ≫ (comapUpperStarIso a g).hom.app L) ≫ θ =
      (p₂)^*⟦Λ⟧.map (finiteFreeLattice a e') ≫ (comapUpperStarIso a p₂).inv.app _ := by
    simp only [θ, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (p₂)^*⟦Λ⟧ ((comapUpperStarIso a g).hom.app L),
      Iso.hom_inv_id_app]
    simp
  rw [hx, Category.assoc c₁, hy, Adjunction.homEquiv_naturality_right_symm,
    (Mod.extendRestrictAdjunction (coefficientMap a P)).homEquiv_naturality_left_symm c₁,
    homEquiv_symm_upperStar_map_finiteFreeLattice,
    homEquiv_symm_upperStar_map_finiteFreeLattice, Functor.map_comp, Functor.map_comp,
    reassoc_of% hc₁, Category.assoc, Category.assoc, ← hTe]

/-- The lattice `Λ_V^n ⟶ f^* Res L` spanned by a basis `e : Λ'_V^n ≅ f^* L`, through the
commutation `Res(f^* L) ≅ f^* Res L`. -/
noncomputable def finiteFreeLatticeUpperStar {S V : Scheme.{u}} {f : V ⟶ S}
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)} {n : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ (f)^*⟦Λ'⟧.obj L) :
    Mod.finiteFree (condensedRingObj Λ V) n ⟶
      (f)^*⟦Λ⟧.obj ((Mod.comap (coefficientMap a S)).obj L) :=
  finiteFreeLattice a e ≫ (comapUpperStarIso a f).hom.app L

/-- The transition isomorphism intertwines the bases through the comparison of the square. -/
lemma upperStar_map_hom_comp_finiteFreeTransition {S V W P : Scheme.{u}} {f : V ⟶ S}
    {g : W ⟶ S} {p₁ : P ⟶ V} {p₂ : P ⟶ W} (h : IsPullback p₁ p₂ f g)
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)} {n m : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ (f)^*⟦Λ'⟧.obj L)
    (e' : Mod.finiteFree (condensedRingObj Λ' W) m ≅ (g)^*⟦Λ'⟧.obj L) :
    (p₁)^*⟦Λ'⟧.map e.hom ≫ (upperStarSquareComparison Λ' h.flip.toCommSq).hom.app L =
      (finiteFreeTransition h e e').hom ≫ (p₂)^*⟦Λ'⟧.map e'.hom := by
  have H := hom_comp_eq_trans_hom_comp ((p₁)^*⟦Λ'⟧.mapIso e)
    ((upperStarSquareComparison Λ' h.flip.toCommSq).app L) ((p₂)^*⟦Λ'⟧.mapIso e'.symm)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.symm_inv] at H
  rw [finiteFreeTransition]
  exact H

/-- The inverse of the transition isomorphism intertwines the bases through the inverse of the
comparison of the square. -/
lemma upperStar_map_hom_comp_finiteFreeTransition_inv {S V W P : Scheme.{u}} {f : V ⟶ S}
    {g : W ⟶ S} {p₁ : P ⟶ V} {p₂ : P ⟶ W} (h : IsPullback p₁ p₂ f g)
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)} {n m : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ (f)^*⟦Λ'⟧.obj L)
    (e' : Mod.finiteFree (condensedRingObj Λ' W) m ≅ (g)^*⟦Λ'⟧.obj L) :
    (p₂)^*⟦Λ'⟧.map e'.hom ≫ (upperStarSquareComparison Λ' h.flip.toCommSq).symm.hom.app L =
      (finiteFreeTransition h e e').inv ≫ (p₁)^*⟦Λ'⟧.map e.hom := by
  have H := inv_comp_eq_trans_inv_comp ((p₁)^*⟦Λ'⟧.mapIso e)
    ((upperStarSquareComparison Λ' h.flip.toCommSq).app L) ((p₂)^*⟦Λ'⟧.mapIso e'.symm)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv] at H
  rw [finiteFreeTransition, Iso.symm_hom]
  exact H

/-- The inverse form of `comapUpperStarIso_comp_upperStarSquareComparison`. -/
lemma comapUpperStarIso_comp_upperStarSquareComparison_symm {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (L : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    (comapUpperStarIso a g').hom.app ((f)^*⟦Λ'⟧.obj L) ≫
        (g')^*⟦Λ⟧.map ((comapUpperStarIso a f).hom.app L) ≫
        (upperStarSquareComparison Λ sq).symm.hom.app ((Mod.comap (coefficientMap a Y)).obj L) =
      (Mod.comap (coefficientMap a X')).map ((upperStarSquareComparison Λ' sq).symm.hom.app L) ≫
        (comapUpperStarIso a f').hom.app ((g)^*⟦Λ'⟧.obj L) ≫
        (f')^*⟦Λ⟧.map ((comapUpperStarIso a g).hom.app L) := by
  rw [← cancel_epi ((Mod.comap (coefficientMap a X')).map
    ((upperStarSquareComparison Λ' sq).hom.app L)),
    ← reassoc_of% (comapUpperStarIso_comp_upperStarSquareComparison a sq L)]
  simp only [Iso.symm_hom, Iso.hom_inv_id_app, ← Functor.map_comp_assoc,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.comp_obj, Category.comp_id]

/-- On a fibre product `V ×_S W`, the cokernels of the pullbacks of the lattices of two bases
whose transition isomorphism and its inverse are defined over `Λ` are isomorphic, compatibly
with the comparison `p₁^* f^* ≅ p₂^* g^*`. -/
lemma exists_iso_upperStar_cokernel_finiteFreeLatticeUpperStar {S V W P : Scheme.{u}}
    {f : V ⟶ S} {g : W ⟶ S} {p₁ : P ⟶ V} {p₂ : P ⟶ W} (h : IsPullback p₁ p₂ f g)
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)} {n m : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ (f)^*⟦Λ'⟧.obj L)
    (e' : Mod.finiteFree (condensedRingObj Λ' W) m ≅ (g)^*⟦Λ'⟧.obj L)
    (hdef : IsDefinedOver a p₁ p₂ (finiteFreeTransition h e e').hom ∧
      IsDefinedOver a p₂ p₁ (finiteFreeTransition h e e').inv) :
    ∃ ψ : (p₁)^*⟦Λ⟧.obj (cokernel (finiteFreeLatticeUpperStar a e)) ≅
      (p₂)^*⟦Λ⟧.obj (cokernel (finiteFreeLatticeUpperStar a e')),
      (p₁)^*⟦Λ⟧.map (cokernel.π (finiteFreeLatticeUpperStar a e)) ≫ ψ.hom =
        (upperStarSquareComparison Λ h.flip.toCommSq).hom.app
          ((Mod.comap (coefficientMap a S)).obj L) ≫
          (p₂)^*⟦Λ⟧.map (cokernel.π (finiteFreeLatticeUpperStar a e')) := by
  obtain ⟨c₁, hc₁⟩ := exists_comp_eq_upperStar_map_finiteFreeLattice a (f := f) (g := g)
    (L := L) p₁ p₂ (upperStarSquareComparison Λ h.flip.toCommSq)
    (upperStarSquareComparison Λ' h.flip.toCommSq)
    (comapUpperStarIso_comp_upperStarSquareComparison a h.flip.toCommSq L) e e'
    (finiteFreeTransition h e e').hom (upperStar_map_hom_comp_finiteFreeTransition h e e')
    hdef.1
  obtain ⟨c₂, hc₂⟩ := exists_comp_eq_upperStar_map_finiteFreeLattice a (f := g) (g := f)
    (L := L) p₂ p₁ (upperStarSquareComparison Λ h.flip.toCommSq).symm
    (upperStarSquareComparison Λ' h.flip.toCommSq).symm
    (comapUpperStarIso_comp_upperStarSquareComparison_symm a h.flip.toCommSq L) e' e
    (finiteFreeTransition h e e').inv (upperStar_map_hom_comp_finiteFreeTransition_inv h e e')
    hdef.2
  have hc₁' : (p₁)^*⟦Λ⟧.map (finiteFreeLatticeUpperStar a e) ≫
      ((upperStarSquareComparison Λ h.flip.toCommSq).app
        ((Mod.comap (coefficientMap a S)).obj L)).hom =
      c₁ ≫ (p₂)^*⟦Λ⟧.map (finiteFreeLatticeUpperStar a e') := by
    rw [Iso.app_hom, finiteFreeLatticeUpperStar, finiteFreeLatticeUpperStar, hc₁]
  have hc₂' : (p₂)^*⟦Λ⟧.map (finiteFreeLatticeUpperStar a e') ≫
      ((upperStarSquareComparison Λ h.flip.toCommSq).app
        ((Mod.comap (coefficientMap a S)).obj L)).inv =
      c₂ ≫ (p₁)^*⟦Λ⟧.map (finiteFreeLatticeUpperStar a e) := by
    rw [Iso.app_inv, ← Iso.symm_hom, finiteFreeLatticeUpperStar, finiteFreeLatticeUpperStar,
      hc₂]
  exact exists_iso_comp_eq_of_isColimit_cokernelCofork_of_factors
    (isColimitOfHasCokernelOfPreservesColimit (p₁)^*⟦Λ⟧ (finiteFreeLatticeUpperStar a e))
    (isColimitOfHasCokernelOfPreservesColimit (p₂)^*⟦Λ⟧ (finiteFreeLatticeUpperStar a e'))
    ((upperStarSquareComparison Λ h.flip.toCommSq).app
      ((Mod.comap (coefficientMap a S)).obj L)) c₁ hc₁' c₂ hc₂'

/-- The lattice of a basis is a monomorphism when the unit `Λ^n ⟶ Res(Λ' ⊗_Λ Λ^n)` is one, and
its adjoint is the isomorphism `Λ' ⊗_Λ Λ^n ≅ Λ'^n ≅ f^* L`. -/
lemma mono_finiteFreeLatticeUpperStar {S V : Scheme.{u}} {f : V ⟶ S}
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)} {n : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ (f)^*⟦Λ'⟧.obj L)
    [Mono ((Mod.extendRestrictAdjunction (coefficientMap a V)).unit.app
      (Mod.finiteFree (condensedRingObj Λ V) n))] :
    Mono (finiteFreeLatticeUpperStar a e) := by
  have : Mono (finiteFreeLattice a e) := by
    rw [finiteFreeLattice, Adjunction.homEquiv_unit]
    infer_instance
  rw [finiteFreeLatticeUpperStar]
  infer_instance

/-- The adjoint of the lattice of a basis `e` is the isomorphism `Λ' ⊗_Λ Λ^n ≅ Λ'^n ≅ f^* L`. -/
lemma isIso_homEquiv_symm_finiteFreeLatticeUpperStar {S V : Scheme.{u}} {f : V ⟶ S}
    {L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S)} {n : ℕ}
    (e : Mod.finiteFree (condensedRingObj Λ' V) n ≅ (f)^*⟦Λ'⟧.obj L) :
    IsIso (((Mod.extendRestrictAdjunction (coefficientMap a V)).homEquiv _ _).symm
      (finiteFreeLatticeUpperStar a e ≫ (comapUpperStarIso a f).inv.app L)) := by
  have h : finiteFreeLatticeUpperStar a e ≫ (comapUpperStarIso a f).inv.app L =
      finiteFreeLattice a e := by
    rw [finiteFreeLatticeUpperStar, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [h, finiteFreeLattice, Equiv.symm_apply_apply]
  infer_instance

/-- **Descent of a locally free module along a change of coefficients, from transition matrices
defined over `Λ`.** See the module docstring. -/
theorem exists_isLocallyFree_extendScalars_iso_of_isDefinedOver {S : Scheme.{u}}
    (L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ' S))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S) [Finite 𝒰.I₀] {n : 𝒰.I₀ → ℕ}
    (e : ∀ k, Mod.finiteFree (condensedRingObj Λ' (𝒰.X k)) (n k) ≅ (𝒰.f k)^*⟦Λ'⟧.obj L)
    {P : 𝒰.I₀ → 𝒰.I₀ → Scheme.{u}} {p₁ : ∀ j k, P j k ⟶ 𝒰.X j} {p₂ : ∀ j k, P j k ⟶ 𝒰.X k}
    (hP : ∀ j k, IsPullback (p₁ j k) (p₂ j k) (𝒰.f j) (𝒰.f k))
    (hmono : ∀ k, Mono ((Mod.extendRestrictAdjunction (coefficientMap a (𝒰.X k))).unit.app
      (Mod.finiteFree (condensedRingObj Λ (𝒰.X k)) (n k))))
    (hdef : ∀ j k,
      IsDefinedOver a (p₁ j k) (p₂ j k) (finiteFreeTransition (hP j k) (e j) (e k)).hom ∧
        IsDefinedOver a (p₂ j k) (p₁ j k) (finiteFreeTransition (hP j k) (e j) (e k)).inv) :
    ∃ L' : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
      IsLocallyFree (condensedRingObj Λ S) L' ∧
        Nonempty ((Mod.extendScalars (coefficientMap a S)).obj L' ≅ L) := by
  choose ψ hψ using fun j k ↦
    exists_iso_upperStar_cokernel_finiteFreeLatticeUpperStar a (hP j k) (e j) (e k) (hdef j k)
  have (k : 𝒰.I₀) : Mono (finiteFreeLatticeUpperStar a (e k)) :=
    have := hmono k
    mono_finiteFreeLatticeUpperStar a (e k)
  exact exists_isLocallyFree_extendScalars_iso_of_cover a L 𝒰
    (fun k ↦ cokernel (finiteFreeLatticeUpperStar a (e k)))
    (fun k ↦ cokernel.π (finiteFreeLatticeUpperStar a (e k))) hP ψ hψ fun k ↦
      ⟨n k, finiteFreeLatticeUpperStar a (e k), cokernel.condition _,
        ⟨Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)⟩,
        isIso_homEquiv_symm_finiteFreeLatticeUpperStar a (e k)⟩

end Glue

end AlgebraicGeometry.ProEtale.CondensedRing
