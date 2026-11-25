/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFacGeneric

/-!
# The derived (Pull) isomorphism through the counits, for an arbitrary coefficient change

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, and
`f : X ⟶ Y` a morphism of schemes. We show that, through the counits of the left derived
functors, the derived (Pull) isomorphism
`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso a f` is the underived (Pull)
isomorphism on every complex `K`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIsoFac`), by unpacking each of its seven
constituents against the counits. As a consequence, the derived (Pull) isomorphisms are
compatible with the composition of derived pullbacks, for every coefficient change
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIsoCompCoherence`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- A chain of rewritings in a category, used to unpack a composite of seven isomorphisms
against counits. -/
lemma comp_eq_of_counit_chain {𝒟 : Type*} [Category* 𝒟]
    {A₀ A₁ A₃ A₄ A₅ A₆ A₇ U V W₅ N₄ X₃ Y₁ Y₂ : 𝒟}
    {m₁ : A₀ ⟶ A₁} {m₃ : A₁ ⟶ A₃} {m₄ : A₃ ⟶ A₄} {m₅ : A₄ ⟶ A₅} {m₆ : A₅ ⟶ A₆} {m₇ : A₆ ⟶ A₇}
    {u₁ : A₇ ⟶ U} {u₂ : U ⟶ V} {w₇ : A₆ ⟶ V} {w₆ : A₅ ⟶ V} {w₅ : A₄ ⟶ W₅} {q₅ : W₅ ⟶ V}
    {n₄ : A₃ ⟶ N₄} {w₄ : N₄ ⟶ W₅} {x₃ : A₁ ⟶ X₃} {m₃' : X₃ ⟶ N₄} {y₁ : X₃ ⟶ Y₁} {y₂ : Y₁ ⟶ Y₂}
    {q : Y₂ ⟶ W₅} {z : A₀ ⟶ Y₁} {r : Y₂ ⟶ V}
    (h₇ : m₇ ≫ u₁ ≫ u₂ = w₇) (h₆ : m₆ ≫ w₇ = w₆) (h₅ : m₅ ≫ w₆ = w₅ ≫ q₅)
    (h₄ : m₄ ≫ w₅ = n₄ ≫ w₄) (h₃ : m₃ ≫ n₄ = x₃ ≫ m₃') (h₃' : m₃' ≫ w₄ = y₁ ≫ y₂ ≫ q)
    (h₁ : m₁ ≫ x₃ ≫ y₁ = z) (h : q ≫ q₅ = r) :
    (m₁ ≫ 𝟙 A₁ ≫ m₃ ≫ m₄ ≫ m₅ ≫ m₆ ≫ m₇) ≫ u₁ ≫ u₂ = z ≫ y₂ ≫ r := by
  simp only [Category.assoc, Category.id_comp]
  rw [h₇, h₆, h₅, reassoc_of% h₄, reassoc_of% h₃, reassoc_of% h₃', ← h,
    ← reassoc_of% h₁]

private lemma Functor.map_comp_comp_of_eq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z} {k : W ⟶ Z}
    (w : f ≫ g ≫ h = k) : F.map f ≫ F.map g ≫ F.map h = F.map k := by
  rw [← F.map_comp, ← F.map_comp, w]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The composition isomorphism `Mod.extendScalarsComp` of extensions of scalars, followed by
the underived (Pull) isomorphism rewritten with the composite `α_f ≫ a_X`, is the underived
(Pull) isomorphism, on the homotopy categories. -/
lemma mapHomotopyCategory_extendScalarsComp_inv_app_comp_mapModUpperStarExtendScalarsIso
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (.up ℤ)) :
    (NatTrans.mapHomotopyCategory
        (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)).inv (.up ℤ)).app
        ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomotopyCategory (.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory (mapModUpperStarExtendScalarsIso a f).hom (.up ℤ)).app K =
    (pullIsoHomotopy a f).app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _ =
    (HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _
  simp only [← Functor.map_comp]
  refine congrArg _ ?_
  ext n : 1
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    mapModUpperStarExtendScalarsIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app, Iso.refl_inv,
    NatTrans.id_app]
  exact Iso.inv_hom_id_app_assoc
    (Mod.extendScalarsComp (condensedPullbackHom Λ f) (coefficientMap a X)) _ _

/-- The first constituent of `derivedUpperStarExtendScalarsIso a f` through the counits:
`L(Ext_{a_X})` applied to `Lf^*_Λ ≅ D(mapMod(f^*)) ⋙ L(Ext_{α_f})` and the counits of
`L(Ext_{α_f})` is `L(Ext_{a_X})` applied to the counit of `Lf^*_Λ`. -/
lemma map_leftDerivedUpperStarIso_hom_app_comp_counit
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (.up ℤ)) :
    L(Mod.extendScalars (coefficientMap a X)).map
        ((leftDerivedUpperStarIso Λ f).hom.app (DerivedCategory.Qh.obj K)) ≫
      (L(Mod.extendScalars (condensedPullbackHom Λ f)) ⋙
          L(Mod.extendScalars (coefficientMap a X))).map
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapDerivedCategoryFactorsh.hom.app K) ≫
      L(Mod.extendScalars (coefficientMap a X)).map
        ((Mod.extendScalars (condensedPullbackHom Λ f)).leftDerivedFunctorCounit.app
          ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomotopyCategory (.up ℤ)).obj
            K)) =
    L(Mod.extendScalars (coefficientMap a X)).map (((f)^*⟦Λ⟧).leftDerivedFunctorCounit.app K) := by
  have h := Functor.leftDerivedFunctorCompMapDerivedCategoryIso_hom_app_Qh
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalars (condensedPullbackHom Λ f)) K
  exact Functor.map_comp_comp_of_eq _ h

-- the instances of the general lemmas are found for each of the categories of module objects
/-- **The derived (Pull) isomorphism through the counits**: for every coefficient change `a` and
every complex `K`, through the counits of the left derived functors,
`derivedUpperStarExtendScalarsIso a f` at `K` is the underived (Pull) isomorphism `pullIso a f`
at `K`. -/
theorem derivedUpperStarExtendScalarsIsoFac
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (.up ℤ)) :
    DerivedUpperStarExtendScalarsIsoFac a f K :=
  comp_eq_of_counit_chain
    (Functor.leftDerivedFunctorIsoMapDerivedCategory_inv_app_comp_map_comp_counit (f)^*⟦Λ'⟧ _
      ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K))
    (Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso_hom_app_Qh
      (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ K)
    (Functor.leftDerivedFunctorIsoOfIso_hom_app_Qh (mapModUpperStarExtendScalarsIso a f) K)
    (Functor.leftDerivedFunctorCompMapDerivedCategoryIso_inv_app_Qh
      ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
      (Mod.extendScalars (condensedPullbackHom Λ f ≫ coefficientMap a X)) K)
    ((Mod.derivedExtendScalarsCompIso (condensedPullbackHom Λ f) (coefficientMap a X) _
      rfl).inv.naturality
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapDerivedCategoryFactorsh.hom.app
          K)).symm
    (Mod.derivedExtendScalarsCompIso_inv_app_Qh_comp_counit (condensedPullbackHom Λ f)
      (coefficientMap a X)
      ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomotopyCategory (.up ℤ)).obj K))
    (map_leftDerivedUpperStarIso_hom_app_comp_counit a f K)
    (by rw [← DerivedCategory.Qh.map_comp,
      mapHomotopyCategory_extendScalarsComp_inv_app_comp_mapModUpperStarExtendScalarsIso])

/-- **Coherence of the derived (Pull) isomorphism for an arbitrary coefficient change**: the
isomorphisms `derivedUpperStarExtendScalarsIso a` are compatible with the composition
isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, with no flatness hypothesis on `a`. -/
theorem derivedUpperStarExtendScalarsIsoCompCoherence :
    DerivedUpperStarExtendScalarsIsoCompCoherence a := fun _ _ _ p q ↦
  derivedUpperStarExtendScalarsIsoCompCoherenceAt_of_fac a p q
    (fun _ _ ↦ derivedUpperStarExtendScalarsIsoFac a p _)
    (fun _ _ ↦ derivedUpperStarExtendScalarsIsoFac a q _)
    (fun _ _ ↦ derivedUpperStarExtendScalarsIsoFac a (p ≫ q) _)

end AlgebraicGeometry.ProEtale.CondensedRing
