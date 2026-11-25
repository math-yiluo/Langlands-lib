/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The change of geometric generic fibre and the unit of `Lg^* ⊣ Rg_*`

Let `φ : M ⟶ N` be a morphism of models and `φ.toCartesian : M ⟶ φ.cartesianModel` the change of
geometric generic fibre of its cartesian factorization (`NearbyCyclesModel.Hom.toCartesian`): the
identity on total spaces, and `g = φ.toCartesian.generic : 𝒳_η̄ ⟶ 𝒴_η̄ ×_𝒴 𝒳` on geometric generic
fibres. Its pullback exchange is, up to isomorphisms, `Li^* Rj'_*` applied to the unit
`G ⟶ Rg_* Lg^* G` of the adjunction `Lg^* ⊣ Rg_*`; it is a split monomorphism at `C` as soon as
this unit is a split monomorphism at `G = Lε'^* C`
(`NearbyCyclesModel.Hom.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit`).

The abstract input (`Adjunction.isSplitMono_mateEquiv_app_of_isSplitMono_unit`) is a statement
about mates: for adjunctions `L_N ⊣ R_N`, `L_M ⊣ R_M`, `L_G ⊣ R_G`, a functor `T ≅ 𝟭` and an
isomorphism `θ : T ⋙ L_M ≅ L_N ⋙ L_G`, the mate `R_N ⋙ T ⟶ L_G ⋙ R_M` of `θ` is a split
monomorphism at `y` as soon as the unit of `L_G ⊣ R_G` is.

The file also collects the formal closure properties of the class of morphisms whose unit is
split at a given complex:

* the unit of an adjunction `L ⊣ R` is a split monomorphism at `G` as soon as `G` is a retract of
  some `R H` (`CategoryTheory.Adjunction.isSplitMono_unit_app_of_retract`);
* split units compose
  (`ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp`,
  `ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp₃`);
* the unit of a universal homeomorphism is an isomorphism (topological invariance,
  `isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism`);

and their consequence for a change of geometric generic fibre `g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂`
universal homeomorphisms
(`NearbyCyclesModel.Hom.isSplitMono_toCart_pullbackExchange_app_of_factor₃`).

These statements were in `TraceFormula.Specialization.NearbySliceInvariants`,
`NearbySliceInvariantsUnit` and `NearbySliceFactorisationUnit`; they are collected here, below
the slice step of Deligne's finiteness theorem, so that the invariance of nearby cycles under
change of trait can use them.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {D E F : Type*} [Category D] [Category E] [Category F]
  {LN : D ⥤ E} {RN : E ⥤ D} {LM : D ⥤ F} {RM : F ⥤ D} {LG : E ⥤ F} {RG : F ⥤ E}
  (adjN : LN ⊣ RN) (adjM : LM ⊣ RM) (adjG : LG ⊣ RG) {T : D ⥤ D}

/-- For a natural isomorphism `e : T ≅ 𝟭`, the components `e_{T x}` and `T(e_x)` agree. -/
lemma _root_.CategoryTheory.Iso.hom_app_obj_eq_map_hom_app (e : T ≅ 𝟭 D) (x : D) :
    e.hom.app (T.obj x) = T.map (e.hom.app x) := by
  rw [← cancel_mono (e.hom.app x)]
  exact (e.hom.naturality (e.hom.app x)).symm

/-- **The mate of an isomorphism `T ⋙ L_M ≅ L_N ⋙ L_G` with `T ≅ 𝟭` against the unit of
`L_G ⊣ R_G`**: the mate `β : R_N ⋙ T ⟶ L_G ⋙ R_M` of `θ`, followed by the comparison
`κ : R_M ⟶ R_N R_G`, is `e ∘ R_N(η_G)`. -/
lemma mateEquiv_app_comp_eq (e : T ≅ 𝟭 D) (θ : T ⋙ LM ⟶ LN ⋙ LG) [IsIso θ] (y : E) :
    (mateEquiv adjN adjM (TwoSquare.mk _ _ _ _ θ)).app y ≫
        (adjN.unit.app (RM.obj (LG.obj y)) ≫ RN.map (adjG.unit.app (LN.obj (RM.obj (LG.obj y))) ≫
          RG.map ((inv (Functor.whiskerRight e.inv LM ≫ θ)).app (RM.obj (LG.obj y)) ≫
            adjM.counit.app (LG.obj y)))) =
      e.hom.app (RN.obj y) ≫ RN.map (adjG.unit.app y) := by
  set φ : LN ⋙ LG ⟶ LM := inv (Functor.whiskerRight e.inv LM ≫ θ) with hφ
  apply (adjN.homEquiv _ _).symm.injective
  apply (adjG.homEquiv _ _).symm.injective
  simp only [Functor.comp_obj, Functor.id_obj, mateEquiv_apply, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp, Functor.map_comp,
    Category.assoc, homEquiv_counit, counit_naturality, counit_naturality_assoc,
    left_triangle_components_assoc, left_triangle_components]
  have key : φ.app (T.obj (RN.obj y)) ≫ θ.app (RN.obj y) =
      LG.map (LN.map (e.hom.app (RN.obj y))) := by
    have h1 : ∀ w, φ.app w = inv (θ.app w) ≫ LM.map (e.hom.app w) := fun w ↦ by
      rw [hφ]
      simp
    rw [h1, Category.assoc, Iso.hom_app_obj_eq_map_hom_app]
    erw [θ.naturality (e.hom.app (RN.obj y))]
    simp
  have hnat := φ.naturality (adjM.unit.app (T.obj (RN.obj y)) ≫ RM.map (θ.app (RN.obj y)) ≫
    RM.map (LG.map (adjN.counit.app y)))
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hnat
  erw [reassoc_of% hnat]
  erw [adjM.counit_naturality (LG.map (adjN.counit.app y))]
  erw [reassoc_of% (adjM.counit_naturality (θ.app (RN.obj y))),
    adjM.left_triangle_components_assoc, reassoc_of% key]

/-- **Splitting the mate by the unit**: for adjunctions `L_N ⊣ R_N`, `L_M ⊣ R_M`, `L_G ⊣ R_G`, a
natural isomorphism `T ≅ 𝟭` and an isomorphism `θ : T ⋙ L_M ⟶ L_N ⋙ L_G`, the mate
`R_N ⋙ T ⟶ L_G ⋙ R_M` of `θ` is a split monomorphism at `y` as soon as the unit
`y ⟶ R_G L_G y` is. -/
lemma isSplitMono_mateEquiv_app_of_isSplitMono_unit (e : T ≅ 𝟭 D) (θ : T ⋙ LM ⟶ LN ⋙ LG)
    [IsIso θ] (y : E) [IsSplitMono (adjG.unit.app y)] :
    IsSplitMono ((mateEquiv adjN adjM (TwoSquare.mk _ _ _ _ θ)).app y) :=
  IsSplitMono.mk' ⟨(adjN.unit.app (RM.obj (LG.obj y)) ≫
    RN.map (adjG.unit.app (LN.obj (RM.obj (LG.obj y))) ≫
      RG.map ((inv (Functor.whiskerRight e.inv LM ≫ θ)).app (RM.obj (LG.obj y)) ≫
        adjM.counit.app (LG.obj y)))) ≫ RN.map (retraction (adjG.unit.app y)) ≫
      e.inv.app (RN.obj y), by
    rw [← Category.assoc, mateEquiv_app_comp_eq adjN adjM adjG e θ y, Category.assoc,
      ← RN.map_comp_assoc,
      IsSplitMono.id, RN.map_id, Category.id_comp, Iso.hom_inv_id_app]; rfl⟩

end CategoryTheory.Adjunction

/-- The shape of the pullback exchange of nearby cycles: a composite
`θ_i(E R_N c) ≫ I_M(β(E c) ≫ R_M(θ_ε c))` with `θ_i`, `θ_ε` isomorphisms is a split monomorphism
as soon as `β(E c)` is. -/
lemma CategoryTheory.isSplitMono_app_whiskerLeft_comp_whiskerRight
    {C₀ C₁ C₂ C₂' C₃ C₄ C₅ C₆ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₂'] [Category C₃] [Category C₄]
    [Category C₅] [Category C₆] (EN : C₀ ⥤ C₁) (RN : C₁ ⥤ C₂) (IM : C₂' ⥤ C₃) (RM : C₄ ⥤ C₂')
    {IN : C₂ ⥤ C₅} {Fp : C₅ ⥤ C₃} {T : C₂ ⥤ C₂'} {LG : C₁ ⥤ C₄} {F : C₀ ⥤ C₆} {EM : C₆ ⥤ C₄}
    (θi : IN ⋙ Fp ⟶ T ⋙ IM) (β : RN ⋙ T ⟶ LG ⋙ RM) (θε : EN ⋙ LG ⟶ F ⋙ EM) (c : C₀)
    (hi : IsIso θi) (hε : IsIso θε) (h : IsSplitMono (β.app (EN.obj c))) :
    IsSplitMono (NatTrans.app (Functor.whiskerLeft (EN ⋙ RN) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε RM) IM :
        (EN ⋙ RN ⋙ IN) ⋙ Fp ⟶ F ⋙ EM ⋙ RM ⋙ IM) c) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- A composite `a ≫ F(b ≫ c)` with `a`, `c` isomorphisms and `b` a split monomorphism is a split
monomorphism. -/
lemma CategoryTheory.isSplitMono_comp_map_comp {C D : Type*} [Category C] [Category D] {x : D}
    {y z w : C} (F : C ⥤ D) (a : x ⟶ F.obj y) (b : y ⟶ z) (c : z ⟶ w) (ha : IsIso a)
    (hb : IsSplitMono b) (hc : IsIso c) : IsSplitMono (a ≫ F.map (b ≫ c)) :=
  inferInstance

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

/-- The pullback exchange of a morphism of models `ψ` is a split monomorphism at `C` as soon as the
base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of its square of geometric generic fibres (the
mate of the pullback comparison) is a split monomorphism at `Lε_N^* C`: the other two factors are
isomorphisms. -/
theorem isSplitMono_pullbackExchange_app_of_isSplitMono_mate (ψ : M.Hom N f f')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsSplitMono ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ ψ.commSq_j).hom).app ((L((N.ε)^*⟦Λ⟧)).obj C))) :
    IsSplitMono ((ψ.pullbackExchange Λ).app C) := by
  have key := isSplitMono_app_whiskerLeft_comp_whiskerRight (L((N.ε)^*⟦Λ⟧)) R((N.j)_*⟦Λ⟧)
    L((M.i)^*⟦Λ⟧) R((M.j)_*⟦Λ⟧) (pullbackSquareComparison Λ ψ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ ψ.commSq_j).hom)
    (pullbackSquareComparison Λ ψ.commSq_ε).hom C inferInstance inferInstance h
  unfold pullbackExchange
  exact_mod_proofs key

/-- **The change of geometric generic fibre is split by the unit**: the pullback exchange of
`φ.toCartesian` is a split monomorphism at `C` as soon as the unit `G ⟶ Rg_* Lg^* G` of the
adjunction
`Lg^* ⊣ Rg_*` of the morphism `g = φ.toCartesian.generic : 𝒳_η̄ ⟶ 𝒴_η̄ ×_𝒴 𝒳` of geometric generic
fibres is a split monomorphism at `G = Lε'^* C`. -/
theorem isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ φ.toCartesian.generic).unit.app
      ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C))) :
    IsSplitMono ((φ.toCartesian.pullbackExchange Λ).app C) := by
  have e : L((φ.toCartesian.total)^*⟦Λ⟧) ≅ 𝟭 _ := by
    rw [toCartesian_total]
    exact leftDerivedUpperStarId Λ _
  exact φ.toCartesian.isSplitMono_pullbackExchange_app_of_isSplitMono_mate Λ C
    (Adjunction.isSplitMono_mateEquiv_app_of_isSplitMono_unit
      (derivedUpperStarLowerStarAdjunction Λ φ.cartesianModel.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (derivedUpperStarLowerStarAdjunction Λ φ.toCartesian.generic) e
      (pullbackSquareComparison Λ φ.toCartesian.commSq_j).hom
        ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C))

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- **Units split at retracts of the image of the right adjoint**: if `G` is a retract of `R H`,
through `s : G ⟶ R H` and `r : R H ⟶ G` with `s ≫ r = 𝟙`, then the unit `G ⟶ R L G` is a split
monomorphism, with retraction `R(s♭) ≫ r` for the adjoint `s♭ : L G ⟶ H` of `s`. -/
lemma isSplitMono_unit_app_of_retract {G : C} {H : D} (s : G ⟶ R.obj H) (r : R.obj H ⟶ G)
    (hsr : s ≫ r = 𝟙 G) : IsSplitMono (adj.unit.app G) :=
  IsSplitMono.mk' ⟨R.map ((adj.homEquiv _ _).symm s) ≫ r, by
    have h1 : adj.unit.app G ≫ R.map ((adj.homEquiv G H).symm s) = s := by
      have h2 := (adj.homEquiv G H).apply_symm_apply s
      rwa [Adjunction.homEquiv_unit] at h2
    rw [reassoc_of% h1, hsr]
    rfl⟩

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Split units compose**: for `a : X ⟶ Y` and `b : Y ⟶ Z`, if the unit of `Lb^* ⊣ Rb_*` is a
split monomorphism at `G` and the unit of `La^* ⊣ Ra_*` is a split monomorphism at `Lb^* G`, then
the unit of `L(a ≫ b)^* ⊣ R(a ≫ b)_*` is a split monomorphism at `G`: `G` is a retract of
`Rb_* Ra_* La^* Lb^* G ≅ R(a ≫ b)_* (La^* Lb^* G)`. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    [IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ b).unit.app G)]
    [IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ a).unit.app (L((b)^*⟦Λ⟧).obj G))] :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ (a ≫ b)).unit.app G) := by
  refine (derivedUpperStarLowerStarAdjunction Λ (a ≫ b)).isSplitMono_unit_app_of_retract
    (H := L((a)^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj G))
    ((derivedUpperStarLowerStarAdjunction Λ b).unit.app G ≫
      R((b)_*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ a).unit.app
        (L((b)^*⟦Λ⟧).obj G)) ≫ (rightDerivedLowerStarComp Λ a b).hom.app _)
    ((rightDerivedLowerStarComp Λ a b).inv.app _ ≫
      R((b)_*⟦Λ⟧).map (retraction ((derivedUpperStarLowerStarAdjunction Λ a).unit.app
        (L((b)^*⟦Λ⟧).obj G))) ≫
      retraction ((derivedUpperStarLowerStarAdjunction Λ b).unit.app G)) ?_
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, IsSplitMono.id]
  simp

/-- **Topological invariance for the unit**: for a universal homeomorphism `r`, the unit of the
derived adjunction `Lr^* ⊣ Rr_*` is an isomorphism, since `Lr^*` is an equivalence. -/
theorem isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism
    {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r] :
    IsIso (derivedUpperStarLowerStarAdjunction Λ r).unit := by
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ r
  have : L((r)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ r).symm
  exact (derivedUpperStarLowerStarAdjunction Λ r).unit_isIso_of_L_fully_faithful

/-- For a universal homeomorphism `r`, the unit of `Lr^* ⊣ Rr_*` is a split monomorphism at every
complex. -/
instance isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_isUniversalHomeomorphism
    {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r]
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ r).unit.app G) :=
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism Λ r
  inferInstance

namespace NearbyCyclesModel

/-- **The change of geometric generic fibre up to a universal homeomorphism**: if the morphism
`g = φ.toCartesian.generic` of geometric generic fibres factors as `g = r ≫ q` with `r` a universal
homeomorphism and the unit of `Lq^* ⊣ Rq_*` is a split monomorphism at `G = Lε'^* C`, then the
pullback exchange of `φ.toCartesian` is a split monomorphism at `C`. -/
theorem Hom.isSplitMono_toCart_pullbackExchange_app_of_factor {X X' Y Y' : Scheme.{u}}
    {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (φ : M.Hom N f f')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    {Z : Scheme.{u}} (r : M.generic ⟶ Z) (q : Z ⟶ φ.cartesianModel.generic)
    [IsUniversalHomeomorphism r] (hrq : r ≫ q = φ.toCartesian.generic)
    (hq : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ q).unit.app
      ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C))) :
    IsSplitMono ((φ.toCartesian.pullbackExchange Λ).app C) := by
  refine φ.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit Λ C ?_
  rw [← hrq]
  exact isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp Λ r q _

end NearbyCyclesModel


/-- **Split units up to universal homeomorphisms on both sides**: for `g = r₁ ≫ q ≫ r₂` with `r₁`
and `r₂` universal homeomorphisms, the unit of `Lg^* ⊣ Rg_*` is a split monomorphism at `G` as
soon as the unit of `Lq^* ⊣ Rq_*` is a split monomorphism at `Lr₂^* G`. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp₃ {X Z₁ Z₂ Y : Scheme.{u}}
    (r₁ : X ⟶ Z₁) (q : Z₁ ⟶ Z₂) (r₂ : Z₂ ⟶ Y) [IsUniversalHomeomorphism r₁]
    [IsUniversalHomeomorphism r₂]
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hq : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ q).unit.app
      ((L((r₂)^*⟦Λ⟧)).obj G))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ (r₁ ≫ q ≫ r₂)).unit.app G) := by
  have := isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp Λ q r₂ G
  exact isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp Λ r₁ (q ≫ r₂) G


namespace NearbyCyclesModel


/-- **The change of geometric generic fibre up to universal homeomorphisms on both sides**: if
`g = φ.toCartesian.generic` factors as `g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂` universal homeomorphisms
and the unit of `Lq^* ⊣ Rq_*` is a split monomorphism at `Lr₂^* Lε'^* C`, then the pullback
exchange of `φ.toCartesian` is a split monomorphism at `C`. -/
theorem Hom.isSplitMono_toCart_pullbackExchange_app_of_factor₃ {X X' Y Y' : Scheme.{u}}
    {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (φ : M.Hom N f f')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    {Z₁ Z₂ : Scheme.{u}} (r₁ : M.generic ⟶ Z₁) (q : Z₁ ⟶ Z₂) (r₂ : Z₂ ⟶ φ.cartesianModel.generic)
    [IsUniversalHomeomorphism r₁] [IsUniversalHomeomorphism r₂]
    (h : r₁ ≫ q ≫ r₂ = φ.toCartesian.generic)
    (hq : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ q).unit.app
      ((L((r₂)^*⟦Λ⟧)).obj ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C)))) :
    IsSplitMono ((φ.toCartesian.pullbackExchange Λ).app C) := by
  refine φ.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit Λ C ?_
  rw [← h]
  exact isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp₃ Λ r₁ q r₂ _ hq
end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
