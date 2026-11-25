/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.Defs

/-!
# Pullbacks of module sheaves along the two sides of a commutative square

Let `R` be a commutative ring and `B` a sheaf of `R`-algebras on `Y_proét`. For a commutative
square of schemes `h₁ ≫ f₁ = h₂ ≫ f₂ : T ⟶ Y`, the two iterated inverse images
`h₁^* f₁^* B` and `h₂^* f₂^* B` of the coefficient ring are identified by an isomorphism of
algebra objects `ProEtale.RingSheaf.squareCoeffHom`, and the two iterated pullbacks of module
sheaves agree up to restriction of scalars along it
(`ProEtale.RingSheaf.upperStarSquareIso`). This is the bookkeeping of coefficient rings needed
for the base change isomorphisms of part (4) of blueprint
`proposition-extension-zero-restriction-closed-subscheme`.

Both iterated pullbacks are compared with the pullback `(h₁ ≫ f₁)^*` by the composition
isomorphisms of pullbacks, which are monoidal; the module-level statement is then
`CategoryTheory.Functor.mapModCompIso` together with the coherence of restriction of scalars.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R]

/-! ### Monoidality of the comparison isomorphisms of pullbacks -/

section Monoidal

variable {S₀ S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ S₀)

/-- The composition isomorphism `h₁_* ⋙ h₂_* ≅ (h₁ ≫ h₂)_*` of pushforwards of sheaves of
`R`-modules is monoidal, being a composition isomorphism of pushforwards along continuous
functors. -/
instance isMonoidal_lowerStarComp_hom :
    NatTrans.IsMonoidal (lowerStarComp (ModuleCat.{u + 1} R) h₁ h₂).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).symm)
    (ModuleCat.{u + 1} R) (Scheme.ProEt.topology S₀) (Scheme.ProEt.topology S)
    (Scheme.ProEt.topology T)).hom)

/-- The composition isomorphism `h₂^* ⋙ h₁^* ≅ (h₁ ≫ h₂)^*` of pullbacks of sheaves of
`R`-modules is monoidal: it is the conjugate of the monoidal composition isomorphism of
pushforwards. -/
instance isMonoidal_upperStarComp_inv :
    NatTrans.IsMonoidal (upperStarComp (ModuleCat.{u + 1} R) h₁ h₂).inv := by
  have h₁' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (h₁ ≫ h₂))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) h₂).comp
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) h₁))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp (ModuleCat.{u + 1} R) h₁ h₂).inv

/-- The isomorphism `g^* ≅ g'^*` of pullbacks of sheaves of `R`-modules along equal morphisms
is monoidal. -/
instance isMonoidal_upperStarCongr_hom {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    NatTrans.IsMonoidal (upperStarCongr (ModuleCat.{u + 1} R) h).hom := by
  subst h
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))

end Monoidal

/-! ### The comparison of coefficient rings -/

variable {T S₁ S₂ Y : Scheme.{u}} (B : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))
  [MonObj B] (f₁ : S₁ ⟶ Y) (f₂ : S₂ ⟶ Y) (h₁ : T ⟶ S₁) (h₂ : T ⟶ S₂)
  (w : h₁ ≫ f₁ = h₂ ≫ f₂)

/-- The monoidal comparison `f₂^* ⋙ h₂^* ⟶ (h₁ ≫ f₁)^*` of pullbacks along the two sides of
a commutative square `h₁ ≫ f₁ = h₂ ≫ f₂`. -/
noncomputable def upperStarSquareHom :
    (f₂)^*[ModuleCat.{u + 1} R] ⋙ (h₂)^*[ModuleCat.{u + 1} R] ⟶
      (h₁ ≫ f₁)^*[ModuleCat.{u + 1} R] :=
  (upperStarComp (ModuleCat.{u + 1} R) h₂ f₂).inv ≫
    (upperStarCongr (ModuleCat.{u + 1} R) w.symm).hom

/-- The comparison `upperStarSquareHom` is a monoidal natural transformation. -/
instance : NatTrans.IsMonoidal (upperStarSquareHom f₁ f₂ h₁ h₂ w (R := R)) := by
  unfold upperStarSquareHom
  infer_instance

/-- The comparison `upperStarSquareHom` is an isomorphism. -/
instance : IsIso (upperStarSquareHom f₁ f₂ h₁ h₂ w (R := R)) := by
  unfold upperStarSquareHom
  infer_instance

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4): for a commutative
square `h₁ ≫ f₁ = h₂ ≫ f₂`, the isomorphism `h₁^* f₁^* B ≅ h₂^* f₂^* B` of the iterated inverse
images of a sheaf of `R`-algebras `B` (a morphism of algebra objects), through `(h₁ ≫ f₁)^* B`. -/
noncomputable def squareCoeffHom :
    (h₁)^*[ModuleCat.{u + 1} R].obj ((f₁)^*[ModuleCat.{u + 1} R].obj B) ⟶
      (h₂)^*[ModuleCat.{u + 1} R].obj ((f₂)^*[ModuleCat.{u + 1} R].obj B) :=
  Functor.compAlgHom _ _ (upperStarComp (ModuleCat.{u + 1} R) h₁ f₁).inv B ≫
    inv (Functor.compAlgHom _ _ (upperStarSquareHom f₁ f₂ h₁ h₂ w) B)

/-- The comparison of coefficient rings `squareCoeffHom` is an isomorphism. -/
instance : IsIso (squareCoeffHom B f₁ f₂ h₁ h₂ w) := by
  unfold squareCoeffHom
  infer_instance

/-- The comparison of coefficient rings `squareCoeffHom` is a morphism of algebra objects. -/
instance : IsMonHom (squareCoeffHom B f₁ f₂ h₁ h₂ w) := by
  unfold squareCoeffHom
  infer_instance

omit [MonObj B] in
/-- `squareCoeffHom` followed by the comparison `h₂^* f₂^* B ⟶ (h₁ ≫ f₁)^* B` is the composition
isomorphism `h₁^* f₁^* B ⟶ (h₁ ≫ f₁)^* B`. -/
lemma squareCoeffHom_comp :
    squareCoeffHom B f₁ f₂ h₁ h₂ w ≫ Functor.compAlgHom _ _ (upperStarSquareHom f₁ f₂ h₁ h₂ w) B =
      Functor.compAlgHom _ _ (upperStarComp (ModuleCat.{u + 1} R) h₁ f₁).inv B := by
  rw [squareCoeffHom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4): for a commutative
square `h₁ ≫ f₁ = h₂ ≫ f₂` and a sheaf of `R`-algebras `B`, the two iterated pullbacks of `B`-module
sheaves agree, up to restriction of scalars along the isomorphism of coefficient rings
`h₁^* f₁^* B ≅ h₂^* f₂^* B` (`ProEtale.RingSheaf.squareCoeffHom`). -/
noncomputable def upperStarSquareIso :
    upperStar B f₁ ⋙ upperStar _ h₁ ≅
      (upperStar B f₂ ⋙ upperStar _ h₂) ⋙ Mod.comap (squareCoeffHom B f₁ f₂ h₁ h₂ w) :=
  Functor.mapModCompIso _ _ (upperStarComp (ModuleCat.{u + 1} R) h₁ f₁).inv B ≪≫
    Functor.isoWhiskerLeft _ ((Mod.comapCongr (squareCoeffHom_comp B f₁ f₂ h₁ h₂ w)).symm ≪≫
      Mod.comapComp _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso _ _ (upperStarSquareHom f₁ f₂ h₁ h₂ w) B).symm
      _

end AlgebraicGeometry.ProEtale.RingSheaf
