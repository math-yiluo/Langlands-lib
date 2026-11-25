/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.NatTransId
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapMulLeft
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarFromPointAdditive

/-!
# Constant global sections of pulled back condensed rings

Let `Λ` be a commutative condensed ring and `φ : K →+* Γ Λ` a ring homomorphism to its global
sections. For a scheme `X`, the pullback `p_X^*` sends `φ a` to a constant global section of
`Λ_X = p_X^* Λ` (`ProEtale.CondensedRing.constRingHom`), so the category of `Λ_X`-module objects
is `K`-linear (`ProEtale.CondensedRing.modLinear`, by `Mod.linearOfRingHom`). The coefficient
morphism `η_f : Λ_Y ⟶ f_* Λ_X` sends constant global sections to constant global sections
(`ProEtale.CondensedRing.constRingHom_hom_comp_condensedPushforwardHom`), hence the pushforward
`f_*` of module objects is `K`-linear (`ProEtale.CondensedRing.linear_lowerStar`), and so is the
derived pushforward `Rf_*` (`ProEtale.CondensedRing.linear_rightDerivedLowerStar`).

If a morphism of commutative condensed rings `a : Λ ⟶ Λ'` makes `Λ'` a finite free `Λ`-module
with a basis of constant global sections, then so does every coefficient change
`a_X : Λ_X ⟶ Λ'_X` (`ProEtale.CondensedRing.isIso_biproductDesc_coefficientMap_globalSmul`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {K : Type*} [Ring K] (φ : K →+* Γ Λ)

/-- The constant global sections of `Λ_X = p_X^* Λ`: a ring homomorphism `K →+* Γ Λ` to the
global sections of the condensed ring `Λ`, followed by the pullback `p_X^*`. -/
noncomputable def constRingHom (X : Scheme.{u}) : K →+* Γ (condensedRingObj Λ X) :=
  haveI := upperStarFromPoint_additive X
  (Γ.mapFunctor (upperStarFromPoint X)).comp φ

lemma constRingHom_hom (X : Scheme.{u}) (a : K) :
    (constRingHom Λ φ X a).hom =
      Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map (φ a).hom :=
  rfl

/-- The `K`-linear structure on `Λ_X`-module objects, `a : K` acting through the constant global
section `p_X^* (φ a)` of `Λ_X`. -/
noncomputable abbrev modLinear (X : Scheme.{u}) :
    Linear K (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  Mod.linearOfRingHom (constRingHom Λ φ X)

/-- The coefficient morphism `η_f : Λ_Y ⟶ f_* Λ_X` sends constant global sections to constant
global sections. -/
lemma constRingHom_hom_comp_condensedPushforwardHom {X Y : Scheme.{u}} (f : X ⟶ Y) (a : K) :
    (constRingHom Λ φ Y a).hom ≫ condensedPushforwardHom Λ f =
      Functor.LaxMonoidal.ε (f)_*[Ab.{u + 1}] ≫
        (f)_*[Ab.{u + 1}].map (constRingHom Λ φ X a).hom := by
  rw [constRingHom_hom, constRingHom_hom, Category.assoc, condensedPushforwardHom]
  exact Adjunction.ε_comp_map_comp_unit_app_comp_map _ _ _ (upperStarFromPointComp f).hom _

/-- The pushforward `f_*` of module objects over `Λ` is `K`-linear. -/
lemma linear_lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := modLinear Λ φ X
    letI := modLinear Λ φ Y
    ((f)_*⟦Λ⟧).Linear K :=
  Mod.linear_mapMod_comp_comap _ _ (constRingHom Λ φ X) (constRingHom Λ φ Y)
    (constRingHom_hom_comp_condensedPushforwardHom Λ φ f)

/-- The derived pushforward `Rf_*` of module objects over `Λ` is `K`-linear. -/
lemma linear_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := modLinear Λ φ X
    letI := modLinear Λ φ Y
    (R((f)_*⟦Λ⟧)).Linear K :=
  letI := modLinear Λ φ X
  letI := modLinear Λ φ Y
  haveI := linear_lowerStar Λ φ f
  Functor.linear_rightDerivedFunctor K _

/-- On the derived category, the action of `a : K` on (the image of) a complex `M` of
`Λ_X`-module objects is the image of the action of the constant global section `p_X^* (φ a)` in
each degree. -/
lemma smul_id_Q_obj {X : Scheme.{u}}
    (M : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (a : K) :
    letI := modLinear Λ φ X
    a • 𝟙 (DerivedCategory.Q.obj M) = DerivedCategory.Q.map
      ((HomologicalComplex.natTransId (Mod.smulNatTrans (constRingHom Λ φ X a).hom)
        (ComplexShape.up ℤ)).app M) := by
  let _ := modLinear Λ φ X
  rw [← DerivedCategory.Q.map_id, ← Functor.map_smul]
  congr 1

end General

section Basis

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {K : Type*} [Ring K]
  (φ : K →+* Γ Λ')

omit [MonObj Λ] [IsCommMonObj Λ] [IsMonHom a] in
/-- **Finite free coefficient changes**: if `b₁, …, bₙ` is a basis of `Λ'` over `Λ` made of
constant global sections, in the sense that `Λⁿ ⟶ Λ'`, `(xᵢ) ↦ ∑ xᵢ φ(bᵢ)`, is an isomorphism,
then so is its pullback `Λ_Xⁿ ⟶ Λ'_X` along `p_X^*`, `bᵢ` acting through the constant global
section `p_X^* φ(bᵢ)`. -/
lemma isIso_biproductDesc_coefficientMap_globalSmul {n : ℕ} (b : Fin n → K)
    (h : IsIso (biproduct.desc fun i ↦ a ≫ Mod.globalSmul (φ (b i)).hom (Mod.regular Λ') :
      ⨁ (fun _ : Fin n ↦ Λ) ⟶ Λ'))
    (X : Scheme.{u}) :
    IsIso (biproduct.desc fun i ↦ coefficientMap a X ≫
      Mod.globalSmul (constRingHom Λ' φ X (b i)).hom (Mod.regular (condensedRingObj Λ' X)) :
        ⨁ (fun _ : Fin n ↦ condensedRingObj Λ X) ⟶ condensedRingObj Λ' X) := by
  have := upperStarFromPoint_additive X
  have e : (fun i ↦ coefficientMap a X ≫ Mod.globalSmul (constRingHom Λ' φ X (b i)).hom
      (Mod.regular (condensedRingObj Λ' X))) = fun i ↦ (upperStarFromPoint X).map
        (a ≫ Mod.globalSmul (φ (b i)).hom (Mod.regular Λ')) := by
    funext i
    rw [Functor.map_comp, constRingHom_hom, Mod.globalSmul_regular_obj]
  rw [e, ← biproduct.mapBiproduct_inv_map_desc]
  exact IsIso.comp_isIso' inferInstance
    (@Functor.map_isIso _ _ _ _ _ _ (upperStarFromPoint X) _ h)

end Basis

end AlgebraicGeometry.ProEtale.CondensedRing
