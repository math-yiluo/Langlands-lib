/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIdentify
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherence

/-!
# The composition isomorphism of derived pushforwards on complexes

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of schemes, the composition isomorphism
`Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of derived pushforwards of module objects
(`ProEtale.CondensedRing.rightDerivedLowerStarComp`), read on the image `Qh K` of a complex
through the units of the right derived functors, is the conjugate on the homotopy categories of
the composition isomorphism of pullbacks
(`ProEtale.CondensedRing.rightDerivedLowerStarComp_hom_app_Qh_fac`).

As a consequence, the coherence of the derived (Pull) isomorphism with the composition
isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` follows from the analogous coherence of
`comapLowerStarIso` on the homotopy categories, together with the representability of every
object by a complex on which the right derived units are isomorphisms
(`ProEtale.CondensedRing.derivedPullIso_hom_app_comp_of_homotopy`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of pullbacks of module objects, on the
homotopy categories. -/
noncomputable abbrev upperStarCompHomotopy :
    ((f ≫ g)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ) ≅
      ((g)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ) ⋙ ((f)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (upperStarComp Λ f g).symm (.up ℤ)).symm

-- the instances of the general lemmas are found for each of the categories of module objects
/-- `upperStarCompHomotopy` is induced by `upperStarComp` on the homotopy categories. -/
lemma upperStarCompHomotopy_hom_app
    (M : HomotopyCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (.up ℤ)) :
    (upperStarCompHomotopy Λ f g).hom.app M =
      (NatTrans.mapHomotopyCategory (upperStarComp Λ f g).hom (.up ℤ)).app M := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  rfl

-- the instances of the general lemmas are found for each of the categories of module objects
/-- `leftDerivedUpperStarComp` on the image `Qh M` of a complex, through the counits of the left
derived functors, is `upperStarCompHomotopy`. -/
lemma leftDerivedUpperStarComp_hom_app_Qh_fac
    (M : HomotopyCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (.up ℤ)) :
    (leftDerivedUpperStarComp Λ f g).hom.app (DerivedCategory.Qh.obj M) ≫
        L((f)^*⟦Λ⟧).map (((g)^*⟦Λ⟧).leftDerivedFunctorCounit.app M) ≫
        ((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app
          ((((g)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj M) =
      ((f ≫ g)^*⟦Λ⟧).leftDerivedFunctorCounit.app M ≫
        DerivedCategory.Qh.map ((upperStarCompHomotopy Λ f g).hom.app M) := by
  rw [upperStarCompHomotopy_hom_app]
  exact Functor.leftDerivedFunctorFactorIso_hom_app_comp_counit (upperStarComp Λ f g) M

-- the instances of the general lemmas are found for each of the categories of module objects
/-- `rightDerivedLowerStarComp` on the image `Qh K` of a complex, through the units of the right
derived functors, is the conjugate of `upperStarCompHomotopy` on the homotopy categories. -/
lemma rightDerivedLowerStarComp_hom_app_Qh_fac
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (.up ℤ)) :
    ((g)_*⟦Λ⟧).rightDerivedFunctorUnit.app ((((f)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        R((g)_*⟦Λ⟧).map (((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app K) ≫
          (rightDerivedLowerStarComp Λ f g).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((conjugateEquiv
          (((upperStarLowerStarAdjunction Λ g).mapHomotopyCategory (.up ℤ)).comp
            ((upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ)))
          ((upperStarLowerStarAdjunction Λ (f ≫ g)).mapHomotopyCategory (.up ℤ))
          (upperStarCompHomotopy Λ f g).hom).app K) ≫
        ((f ≫ g)_*⟦Λ⟧).rightDerivedFunctorUnit.app K :=
  Adjunction.conjugateEquiv_comp_app_fac
    (adj'_f := derivedUpperStarLowerStarAdjunction Λ f)
    (adj'_g := derivedUpperStarLowerStarAdjunction Λ g)
    (adj'_fg := derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (c := upperStarCompHomotopy Λ f g) (c' := leftDerivedUpperStarComp Λ f g)
    (adj_f := (upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ))
    (adj_g := (upperStarLowerStarAdjunction Λ g).mapHomotopyCategory (.up ℤ))
    (adj_fg := (upperStarLowerStarAdjunction Λ (f ≫ g)).mapHomotopyCategory (.up ℤ))
    (hc := leftDerivedUpperStarComp_hom_app_Qh_fac Λ f g)
    (hη := fun M ↦
      ((upperStarLowerStarAdjunction Λ (f ≫ g)).mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ _) _ _ M)
    (hε_f := fun N ↦
      ((upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ _) _ _ N)
    (hε_g := fun N ↦
      ((upperStarLowerStarAdjunction Λ g).mapHomotopyCategory (.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ _) _ _ N) (K := K)

/-- The conjugate of `upperStarCompHomotopy` on the homotopy categories:
`f_* ⋙ g_* ⟶ (f ≫ g)_*` on homotopy categories of module objects. -/
noncomputable abbrev lowerStarCompHomotopy :
    ((f)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ) ⋙ ((g)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ) ⟶
      ((f ≫ g)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ) :=
  conjugateEquiv
    (((upperStarLowerStarAdjunction Λ g).mapHomotopyCategory (.up ℤ)).comp
      ((upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ)))
    ((upperStarLowerStarAdjunction Λ (f ≫ g)).mapHomotopyCategory (.up ℤ))
    (upperStarCompHomotopy Λ f g).hom

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

-- the instances of the general lemmas are found for each of the categories of module objects
/-- The coherence of `derivedComapLowerStarIso` with the composition isomorphisms of derived
pushforwards follows from its analogue on the homotopy categories, given that every object of
the derived category is represented by a complex on which the right derived units of
`f_* ⋙ g_*` are isomorphisms (e.g. a K-injective complex). -/
lemma derivedComapLowerStarIsoCompCoherence_of_homotopy
    (hH : ∀ K, ((Mod.comap (coefficientMap a Z)).mapHomotopyCategory (.up ℤ)).map
        ((lowerStarCompHomotopy Λ' f g).app K) ≫
        (NatTrans.mapHomotopyCategory (comapLowerStarIso a (f ≫ g)).hom (.up ℤ)).app K =
      (NatTrans.mapHomotopyCategory (comapLowerStarIso a g).hom (.up ℤ)).app
          ((((f)_*⟦Λ'⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        (((g)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom (.up ℤ)).app K) ≫
        (lowerStarCompHomotopy Λ f g).app
          (((Mod.comap (coefficientMap a X)).mapHomotopyCategory (.up ℤ)).obj K))
    (hK : ∀ N, ∃ K, Nonempty (N ≅ DerivedCategory.Qh.obj K) ∧
      IsIso (((g)_*⟦Λ'⟧).rightDerivedFunctorUnit.app
          ((((f)_*⟦Λ'⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        R((g)_*⟦Λ'⟧).map (((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app K))) :
    DerivedComapLowerStarIsoCompCoherence a f g :=
  Adjunction.comp_coherence_app_of_isIso
    (β'_f := ((f)_*⟦Λ'⟧).rightDerivedFunctorUnit) (β'_g := ((g)_*⟦Λ'⟧).rightDerivedFunctorUnit)
    (β'_fg := ((f ≫ g)_*⟦Λ'⟧).rightDerivedFunctorUnit)
    (β_f := ((f)_*⟦Λ⟧).rightDerivedFunctorUnit) (β_g := ((g)_*⟦Λ⟧).rightDerivedFunctorUnit)
    (β_fg := ((f ≫ g)_*⟦Λ⟧).rightDerivedFunctorUnit)
    (φ_X := (Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh)
    (φ_Y := (Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh)
    (φ_Z := (Mod.comap (coefficientMap a Z)).mapDerivedCategoryFactorsh)
    (E_f := derivedComapLowerStarIso a f) (E_g := derivedComapLowerStarIso a g)
    (E_fg := derivedComapLowerStarIso a (f ≫ g))
    (e_f := fun K ↦ (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom (.up ℤ)).app K)
    (e_g := fun K ↦ (NatTrans.mapHomotopyCategory (comapLowerStarIso a g).hom (.up ℤ)).app K)
    (e_fg := fun K ↦
      (NatTrans.mapHomotopyCategory (comapLowerStarIso a (f ≫ g)).hom (.up ℤ)).app K)
    (d' := (rightDerivedLowerStarComp Λ' f g).hom) (d := (rightDerivedLowerStarComp Λ f g).hom)
    (d'_h := (lowerStarCompHomotopy Λ' f g).app) (d_h := (lowerStarCompHomotopy Λ f g).app)
    (hE_f := derivedComapLowerStarIso_hom_app_Qh a f)
    (hE_g := derivedComapLowerStarIso_hom_app_Qh a g)
    (hE_fg := derivedComapLowerStarIso_hom_app_Qh a (f ≫ g))
    (hd' := rightDerivedLowerStarComp_hom_app_Qh_fac Λ' f g)
    (hd := rightDerivedLowerStarComp_hom_app_Qh_fac Λ f g) (hH := hH) (hK := hK)

-- the instances of the general lemmas are found for each of the categories of module objects
/-- The derived (Pull) isomorphisms are compatible with the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, given the hypotheses of
`derivedComapLowerStarIsoCompCoherence_of_homotopy`. -/
lemma derivedPullIso_hom_app_comp_of_homotopy
    (hH : ∀ K, ((Mod.comap (coefficientMap a Z)).mapHomotopyCategory (.up ℤ)).map
        ((lowerStarCompHomotopy Λ' f g).app K) ≫
        (NatTrans.mapHomotopyCategory (comapLowerStarIso a (f ≫ g)).hom (.up ℤ)).app K =
      (NatTrans.mapHomotopyCategory (comapLowerStarIso a g).hom (.up ℤ)).app
          ((((f)_*⟦Λ'⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        (((g)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom (.up ℤ)).app K) ≫
        (lowerStarCompHomotopy Λ f g).app
          (((Mod.comap (coefficientMap a X)).mapHomotopyCategory (.up ℤ)).obj K))
    (hK : ∀ N, ∃ K, Nonempty (N ≅ DerivedCategory.Qh.obj K) ∧
      IsIso (((g)_*⟦Λ'⟧).rightDerivedFunctorUnit.app
          ((((f)_*⟦Λ'⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        R((g)_*⟦Λ'⟧).map (((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app K)))
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (derivedPullIso a (f ≫ g)).hom.app M ≫
        (leftDerivedUpperStarComp Λ' f g).hom.app
          (L(Mod.extendScalars (coefficientMap a Z)).obj M) =
      L(Mod.extendScalars (coefficientMap a X)).map
          ((leftDerivedUpperStarComp Λ f g).hom.app M) ≫
        (derivedPullIso a f).hom.app (L((g)^*⟦Λ⟧).obj M) ≫
          L((f)^*⟦Λ'⟧).map ((derivedPullIso a g).hom.app M) :=
  derivedPullIso_hom_app_comp_of_derivedComapLowerStarIso a f g
    (derivedComapLowerStarIsoCompCoherence_of_homotopy Λ f g a hH hK) M

end AlgebraicGeometry.ProEtale.CondensedRing
