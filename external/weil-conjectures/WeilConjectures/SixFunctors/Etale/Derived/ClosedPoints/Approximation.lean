/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Vanishing

/-!
# Approximation of a sheaf supported at closed points

Let `X` be locally of finite type over a field and `F` an étale sheaf of `Λ`-modules on `X`
whose stalks vanish at the non-closed points. For a finite set `S` of closed points let
`F_S ⊆ F` be the subsheaf of sections supported on `S`. These subsheaves form a filtered
diagram indexed by the finite sets of closed points, and `F` is its colimit (blueprint
`lemma-sheaves-finite-support-finite-morphisms--1`).

## Main definitions

- `AlgebraicGeometry.Etale.FiniteClosedPoints`: the finite sets of closed points, ordered by
  inclusion.
- `AlgebraicGeometry.Etale.supportedSectionsFunctor`: the diagram `S ↦ F_S`.

## Main statements

- `AlgebraicGeometry.Etale.isColimitSupportedSectionsCocone`
(`lemma-sheaves-finite-support-finite-morphisms--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The finite sets of closed points of a scheme, ordered by inclusion. -/
def FiniteClosedPoints (X : Scheme.{u}) : Type u :=
  {S : Set X // S.Finite ∧ S ⊆ closedPoints X}

namespace FiniteClosedPoints

variable {X : Scheme.{u}}

instance : PartialOrder (FiniteClosedPoints X) :=
  inferInstanceAs (PartialOrder {S : Set X // S.Finite ∧ S ⊆ closedPoints X})

instance : IsDirectedOrder (FiniteClosedPoints X) :=
  ⟨fun S T ↦ ⟨⟨S.1 ∪ T.1, S.2.1.union T.2.1, Set.union_subset S.2.2 T.2.2⟩,
    Set.subset_union_left, Set.subset_union_right⟩⟩

instance : Nonempty (FiniteClosedPoints X) := ⟨⟨∅, Set.finite_empty, Set.empty_subset _⟩⟩

/-- The open complement of a finite set of closed points. -/
abbrev openCompl (S : FiniteClosedPoints X) : X.Opens := openComplOfFinite S.2.1 S.2.2

lemma openCompl_le {S T : FiniteClosedPoints X} (h : S ≤ T) : openCompl T ≤ openCompl S :=
  fun _ hx hxS ↦ hx (h hxS)

end FiniteClosedPoints

open FiniteClosedPoints

section

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The counit `W ×_X U ⟶ W` hits every point of `W` lying over `U`. -/
lemma mem_range_mapPullbackAdj_counit_app_left (U : X.Opens) (W : X.Etale) (w : W.left)
    (hw : W.hom w ∈ U) :
    w ∈ Set.range ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ U.ι inferInstance
      trivial).counit.app W).left := by
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.hom) (g := U.ι) w
    ⟨W.hom w, hw⟩ rfl
  exact ⟨p, hp⟩

/-- Sections supported on `S` are supported on every larger `T`. -/
lemma supportedSectionsι_comp_unit_of_le {S T : FiniteClosedPoints X} (h : S ≤ T) :
    supportedSectionsι F (openCompl S) ≫
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (openCompl T).ι).unit.app F = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ ModuleCat.hom_ext
    (LinearMap.ext fun z ↦ ?_)))
  let y := (supportedSectionsι F (openCompl S)).hom.app W z
  have hy : F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (openCompl S).ι
      inferInstance trivial).counit.app W.unop).op y = 0 := by
    refine (congrArg (fun φ ↦ φ.hom.app W z)
      (supportedSectionsι_comp_unit F (openCompl S))).trans ?_
    simp
  let c := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (openCompl T).ι inferInstance
    trivial).counit.app W.unop
  have key : F.obj.map c.op y = 0 := by
    refine eq_zero_of_forall_mem_sectionVanishingLocus (F := F) fun v ↦
      mem_sectionVanishingLocus_map c ⟨_, _, mem_range_mapPullbackAdj_counit_app_left _ _ _
        (openCompl_le h ?_), hy⟩
    have h₁ := MorphismProperty.Over.w c
    have h₂ := congrArg (fun f ↦ f v) h₁
    simp only [Scheme.Hom.comp_apply] at h₂
    have h₃ : W.unop.hom (c.left v) = _ := h₂
    rw [h₃, ← SetLike.mem_coe, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  exact key.trans (by simp)

/-- The diagram `S ↦ F_S` of the subsheaves of sections supported on finite sets of closed
points. -/
noncomputable def supportedSectionsFunctor :
    FiniteClosedPoints X ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj S := supportedSections F (openCompl S)
  map {S T} h := kernel.lift _ (supportedSectionsι F (openCompl S))
    (supportedSectionsι_comp_unit_of_le F (leOfHom h))
  map_id S := by
    refine (cancel_mono (supportedSectionsι F (openCompl S))).1 ?_
    rw [Category.id_comp]
    exact kernel.lift_ι _ _ _
  map_comp {S T R} f g := by
    refine (cancel_mono (supportedSectionsι F (openCompl R))).1 ?_
    simp [supportedSectionsι]

@[reassoc (attr := simp)]
lemma supportedSectionsFunctor_map_ι {S T : FiniteClosedPoints X} (h : S ⟶ T) :
    (supportedSectionsFunctor F).map h ≫ supportedSectionsι F (openCompl T) =
      supportedSectionsι F (openCompl S) :=
  kernel.lift_ι _ _ _

/-- The cocone with point `F` over the diagram `S ↦ F_S`, reindexed to a small category. -/
@[simps]
noncomputable def supportedSectionsCocone :
    Cocone (AsSmall.down ⋙ supportedSectionsFunctor F) where
  pt := F
  ι := { app S := supportedSectionsι F (openCompl (AsSmall.down.obj S)) }

end

attribute [local instance] IsFiltered.isConnected

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1`: **approximation of a sheaf
supported at closed points.** Let `X` be locally of finite type over a field and `F` an étale sheaf
of `Λ`-modules on `X` whose stalks vanish at the non-closed points. Then `F` is the filtered colimit
of its subsheaves `F_S` of sections supported on finite sets `S` of closed points, and each `F_S`
vanishes off `S` (`AlgebraicGeometry.Etale.isZero_upperStar_supportedSections`), so it is the
pushforward of a sheaf on the closed subscheme `S`
(`AlgebraicGeometry.Etale.mem_essImage_lowerStar_iff_isZero_sheafFiber`,
`proposition-extension-zero-restriction-closed-subscheme--5`).

The blueprint uses the finitely generated subsheaves of `F` instead; the `F_S` play the same
role. The comparison `colim F_S ⟶ F` is a monomorphism, filtered colimits being exact, and an
epimorphism since every section of `F` is étale locally a section of some `F_S`
(`AlgebraicGeometry.Etale.exists_supportedSectionsι_app_eq_map`). -/
noncomputable def isColimitSupportedSectionsCocone {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)) :
    IsColimit (supportedSectionsCocone F) := by
  let D := AsSmall.down ⋙ supportedSectionsFunctor F
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    IsGrothendieckAbelian.hasColimits _
  have : IsFiltered (AsSmall.{u + 1} (FiniteClosedPoints X)) :=
    IsFiltered.of_equivalence AsSmall.equiv
  have : HasColimitsOfShape (AsSmall.{u + 1} (FiniteClosedPoints X))
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : HasColimit D := HasColimitsOfShape.has_colimit D
  let t := colimit.desc D (supportedSectionsCocone F)
  let α : D ⟶ (Functor.const _).obj F := (supportedSectionsCocone F).ι
  have (S : AsSmall.{u + 1} (FiniteClosedPoints X)) : Mono (α.app S) :=
    inferInstanceAs (Mono (supportedSectionsι F _))
  have : Mono α := NatTrans.mono_of_mono_app α
  have ht : Mono t :=
    colim.map_mono' α (colimit.isColimit D) (isColimitConstCocone _ F) t
      (fun S ↦ by simp [t, α])
  have : Epi t := by
    refine (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u + 1} Λ) t).1 ⟨fun {W} s ↦ ?_⟩
    rw [mem_smallEtaleTopology_iff]
    intro w
    obtain ⟨V, g, hw, S, hSf, hSc, z, hz⟩ := exists_supportedSectionsι_app_eq_map F p hF s w
    let S' : FiniteClosedPoints X := ⟨S, hSf, hSc⟩
    refine ⟨V, g, ⟨(colimit.ι D (AsSmall.up.obj S')).hom.app (op V) z, ?_⟩, hw⟩
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, colimit.ι_desc]
    exact hz
  have : IsIso t := isIso_of_mono_of_epi t
  exact IsColimit.ofPointIso (colimit.isColimit D) (i := this)

end Etale

end AlgebraicGeometry
