/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Coherence of the derived (Pull) isomorphism with composition

We discharge the two hypotheses of
`ProEtale.CondensedRing.derivedPullIso_hom_app_comp_of_homotopy`, obtaining the coherence of the
derived (Pull) isomorphism `derivedPullIso a` with the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` for every flat coefficient change `a : Λ ⟶ Λ'`
(`ProEtale.CondensedRing.derivedPullIso_hom_app_comp`).

* The conjugate of the composition isomorphism of pullbacks on the homotopy categories,
  `lowerStarCompHomotopy`, is induced by the composition isomorphism `lowerStarComp` of
  pushforwards (`ProEtale.CondensedRing.lowerStarCompHomotopy_app`): the conjugate on the
  homotopy categories is computed degreewise
  (`CategoryTheory.Adjunction.conjugateEquiv_mapHomotopyCategoryCompIso_app_quotient`), and the
  conjugate of `upperStarComp` is `lowerStarComp` by definition. The underived coherence of
  `comapLowerStarIso` with `lowerStarComp` holds since both are identities on underlying sheaves
  up to the composition isomorphism of pushforwards of sheaves.
* Every object of the derived category is the image of a K-injective complex `K`; the
  pushforward `f_*` preserves K-injective complexes, its left adjoint being exact, so the right
  derived units of `f_*` and `g_*` are isomorphisms at `K` and `f_* K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C_X C_Y C_Z : Type*} [Category* C_X] [Category* C_Y] [Category* C_Z]
  [Preadditive C_X] [Preadditive C_Y] [Preadditive C_Z] {J : Type*} (c : ComplexShape J)
  [(HomotopyCategory.quotient C_X c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C_X c)]
  [(HomotopyCategory.quotient C_Y c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C_Y c)]
  [(HomotopyCategory.quotient C_Z c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C_Z c)]
  {G_f : C_Y ⥤ C_X} {F_f : C_X ⥤ C_Y} (adj_f : G_f ⊣ F_f)
  {G_g : C_Z ⥤ C_Y} {F_g : C_Y ⥤ C_Z} (adj_g : G_g ⊣ F_g)
  {G_fg : C_Z ⥤ C_X} {F_fg : C_X ⥤ C_Z} (adj_fg : G_fg ⊣ F_fg)
  [G_f.Additive] [F_f.Additive] [G_g.Additive] [F_g.Additive] [G_fg.Additive] [F_fg.Additive]

/-- The conjugate, on the homotopy categories, of the isomorphism induced by an isomorphism
`e : G_fg ≅ G_g ⋙ G_f` of left adjoints is computed degreewise on the image of a complex: it is
induced by the conjugate of `e`. -/
lemma conjugateEquiv_mapHomotopyCategoryCompIso_app_quotient (e : G_fg ≅ G_g ⋙ G_f)
    (K : HomologicalComplex C_X c) :
    (conjugateEquiv ((adj_g.mapHomotopyCategory c).comp (adj_f.mapHomotopyCategory c))
        (adj_fg.mapHomotopyCategory c)
        (Functor.mapHomotopyCategoryCompIso e.symm c).symm.hom).app
          ((HomotopyCategory.quotient C_X c).obj K) =
      (HomotopyCategory.quotient C_Z c).map
        ((NatTrans.mapHomologicalComplex (conjugateEquiv (adj_g.comp adj_f) adj_fg e.hom) c).app
          K) := by
  have h₁ : (adj_fg.mapHomotopyCategory c).unit.app ((F_g.mapHomotopyCategory c).obj
      ((F_f.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C_X c).obj K))) =
      (HomotopyCategory.quotient C_Z c).map ((adj_fg.mapHomologicalComplex c).unit.app
        ((F_g.mapHomologicalComplex c).obj ((F_f.mapHomologicalComplex c).obj K))) :=
    mapHomotopyCategory_unit_app_quotient c adj_fg _
  have h₂ : (adj_g.mapHomotopyCategory c).counit.app
      ((F_f.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C_X c).obj K)) =
      (HomotopyCategory.quotient C_Y c).map ((adj_g.mapHomologicalComplex c).counit.app
        ((F_f.mapHomologicalComplex c).obj K)) :=
    mapHomotopyCategory_counit_app_quotient c adj_g _
  have h₃ : (adj_f.mapHomotopyCategory c).counit.app ((HomotopyCategory.quotient C_X c).obj K) =
      (HomotopyCategory.quotient C_X c).map ((adj_f.mapHomologicalComplex c).counit.app K) :=
    mapHomotopyCategory_counit_app_quotient c adj_f _
  have h₄ : (Functor.mapHomotopyCategoryCompIso e.symm c).symm.hom.app
      ((F_g.mapHomotopyCategory c).obj
        ((F_f.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C_X c).obj K))) =
      (HomotopyCategory.quotient C_X c).map ((NatTrans.mapHomologicalComplex e.hom c).app
        ((F_g.mapHomologicalComplex c).obj ((F_f.mapHomologicalComplex c).obj K))) :=
    rfl
  have hR : (NatTrans.mapHomologicalComplex (conjugateEquiv (adj_g.comp adj_f) adj_fg e.hom)
      c).app K = (adj_fg.mapHomologicalComplex c).unit.app
        ((F_g.mapHomologicalComplex c).obj ((F_f.mapHomologicalComplex c).obj K)) ≫
      (F_fg.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex e.hom c).app
        ((F_g.mapHomologicalComplex c).obj ((F_f.mapHomologicalComplex c).obj K)) ≫
        (G_f.mapHomologicalComplex c).map ((adj_g.mapHomologicalComplex c).counit.app
          ((F_f.mapHomologicalComplex c).obj K)) ≫
        (adj_f.mapHomologicalComplex c).counit.app K) := by
    ext n
    simp [conjugateEquiv_apply_app, Adjunction.mapHomologicalComplex]
  rw [hR, conjugateEquiv_apply_app, comp_counit_app]
  simp only [Functor.comp_obj]
  rw [h₁, h₂, h₃, h₄]
  simp only [Functor.map_comp]
  rfl

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The conjugate of the composition isomorphism `upperStarComp` of pullbacks of module objects
is the composition isomorphism `lowerStarComp` of pushforwards. -/
lemma conjugateEquiv_upperStarComp_hom_eq_lowerStarComp :
    conjugateEquiv ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
      (upperStarLowerStarAdjunction Λ (f ≫ g)) (upperStarComp Λ f g).hom =
      (lowerStarComp Λ f g).hom :=
  (conjugateEquiv _ _).apply_symm_apply _

-- the instances of the general lemmas are found for each of the categories of module objects
/-- `lowerStarCompHomotopy` is induced by the composition isomorphism `lowerStarComp` of
pushforwards of module objects. -/
lemma lowerStarCompHomotopy_app
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (.up ℤ)) :
    (lowerStarCompHomotopy Λ f g).app K =
      (NatTrans.mapHomotopyCategory (lowerStarComp Λ f g).hom (.up ℤ)).app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [lowerStarCompHomotopy, Adjunction.conjugateEquiv_mapHomotopyCategoryCompIso_app_quotient,
    conjugateEquiv_upperStarComp_hom_eq_lowerStarComp]
  rfl

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
/-- The underlying morphisms of the components of `comapLowerStarIso` are identities. -/
lemma comapLowerStarIso_hom_app_hom
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    ((comapLowerStarIso a f).hom.app N).hom = 𝟙 _ :=
  Mod.comapMapModComapIso_hom_app_hom ..

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
/-- The underived coherence of `comapLowerStarIso` with the composition isomorphisms
`lowerStarComp` of pushforwards: on underlying sheaves, both sides are the composition
isomorphism of pushforwards of sheaves. -/
lemma comapLowerStarIso_hom_app_lowerStarComp
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    (Mod.comap (coefficientMap a Z)).map ((lowerStarComp Λ' f g).hom.app N) ≫
        (comapLowerStarIso a (f ≫ g)).hom.app N =
      (comapLowerStarIso a g).hom.app ((f)_*⟦Λ'⟧.obj N) ≫
        (g)_*⟦Λ⟧.map ((comapLowerStarIso a f).hom.app N) ≫
          (lowerStarComp Λ f g).hom.app ((Mod.comap (coefficientMap a X)).obj N) := by
  have hmap : ∀ {N₁ N₂ : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (φ : N₁ ⟶ N₂), ((g)_*⟦Λ⟧.map φ).hom = (g)_*[Ab.{u + 1}].map φ.hom := fun _ ↦ rfl
  apply Mod.hom_ext
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom', hmap, comapLowerStarIso_hom_app_hom,
    comapLowerStarIso_hom_app_hom, comapLowerStarIso_hom_app_hom]
  rfl

-- the instances of the general lemmas are found for each of the categories of module objects
/-- The coherence of `comapLowerStarIso` with `lowerStarCompHomotopy` on the homotopy
categories: the hypothesis `hH` of `derivedPullIso_hom_app_comp_of_homotopy`. -/
lemma comapLowerStarIso_lowerStarCompHomotopy
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
      (.up ℤ)) :
    ((Mod.comap (coefficientMap a Z)).mapHomotopyCategory (.up ℤ)).map
        ((lowerStarCompHomotopy Λ' f g).app K) ≫
        (NatTrans.mapHomotopyCategory (comapLowerStarIso a (f ≫ g)).hom (.up ℤ)).app K =
      (NatTrans.mapHomotopyCategory (comapLowerStarIso a g).hom (.up ℤ)).app
          ((((f)_*⟦Λ'⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        (((g)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom (.up ℤ)).app K) ≫
        (lowerStarCompHomotopy Λ f g).app
          (((Mod.comap (coefficientMap a X)).mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [lowerStarCompHomotopy_app, lowerStarCompHomotopy_app]
  change (HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _ =
    (HomotopyCategory.quotient _ _).map _ ≫ (HomotopyCategory.quotient _ _).map _ ≫
      (HomotopyCategory.quotient _ _).map _
  simp only [← Functor.map_comp]
  refine congrArg _ ?_
  ext n : 1
  exact comapLowerStarIso_hom_app_lowerStarComp Λ f g a (K.X n)

-- the instances of the general lemmas are found for each of the categories of module objects
/-- Every object of the derived category is the image of a complex on which the right derived
units of `f_* ⋙ g_*` are isomorphisms, namely a K-injective complex: the hypothesis `hK` of
`derivedPullIso_hom_app_comp_of_homotopy`. -/
lemma exists_iso_Qh_obj_isIso_rightDerivedFunctorUnit_lowerStar
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    ∃ K, Nonempty (N ≅ DerivedCategory.Qh.obj K) ∧
      IsIso (((g)_*⟦Λ⟧).rightDerivedFunctorUnit.app
          ((((f)_*⟦Λ⟧).mapHomotopyCategory (.up ℤ)).obj K) ≫
        R((g)_*⟦Λ⟧).map (((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app K)) := by
  obtain ⟨I, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have := (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
  have : CochainComplex.IsKInjective ((((f)_*⟦Λ⟧).mapHomologicalComplex (.up ℤ)).obj I) :=
    Functor.PreservesKInjectiveComplexes.isKInjective_map I
  refine ⟨(HomotopyCategory.quotient _ _).obj I,
    ⟨e ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm⟩, ?_⟩
  have : IsIso (((g)_*⟦Λ⟧).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
      ((((f)_*⟦Λ⟧).mapHomologicalComplex (.up ℤ)).obj I))) := inferInstance
  exact IsIso.comp_isIso' this inferInstance

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

-- the instances of the general lemmas are found for each of the categories of module objects
/-- The derived (Pull) isomorphisms for a flat coefficient change are compatible with the
composition isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`. -/
theorem derivedPullIso_hom_app_comp
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (derivedPullIso a (f ≫ g)).hom.app M ≫
        (leftDerivedUpperStarComp Λ' f g).hom.app
          (L(Mod.extendScalars (coefficientMap a Z)).obj M) =
      L(Mod.extendScalars (coefficientMap a X)).map
          ((leftDerivedUpperStarComp Λ f g).hom.app M) ≫
        (derivedPullIso a f).hom.app (L((g)^*⟦Λ⟧).obj M) ≫
          L((f)^*⟦Λ'⟧).map ((derivedPullIso a g).hom.app M) :=
  derivedPullIso_hom_app_comp_of_homotopy Λ f g a
    (comapLowerStarIso_lowerStarCompHomotopy Λ f g a)
    (exists_iso_Qh_obj_isIso_rightDerivedFunctorUnit_lowerStar Λ' f g) M

end AlgebraicGeometry.ProEtale.CondensedRing
