/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Composition
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# The open–closed dévissage for generic constructibility

Let `j : X ⟶ Y` be a morphism of `S`-schemes, `v : V ⟶ X` an open immersion with closed
complement `i : W ⟶ X`, and `K` a bounded below complex on `X`. Complete the unit of
`v^* ⊣ Rv_*` to a distinguished triangle

`K ⟶ Rv_* v^* K ⟶ Δ ⟶ K[1]`.

Its third vertex is supported on `W`: `Δ ≅ Ri_* i^* Δ`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStarPlus_of_distTriang_unit`). If the
direct images of `v^* K` along `v` and along `v ≫ j`, and the direct image of `i^* Δ` along
`i ≫ j`, are bounded constructible and commute with base change, and `i^* Δ` is bounded
constructible, then the direct image of `K` along `j` is bounded constructible and commutes with
base change (`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_distTriang_unit`). This is
the third step of the proof of `theorem-generic-constructibility-base-change-rj`, once the second
step has been applied to `v` and to `v ≫ j` and the induction hypothesis to `i ≫ j`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- For an open immersion `v`, the counit `v^* Rv_* ⟶ 𝟭` of the bounded below derived adjunction
is an isomorphism: on a complex of injective sheaves it is the underived counit `v^* v_* ⟶ 𝟭`,
an isomorphism for an open immersion. -/
instance isIso_derivedPlus_counit_of_isOpenImmersion {V X : Scheme.{u}} (v : V ⟶ X)
    [IsOpenImmersion v] :
    IsIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).derivedPlus.counit := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
  obtain ⟨n, hn⟩ := N.2
  have : N.IsGE n := (N.isGE_ι_obj_iff n).1 hn
  obtain ⟨L, _, ⟨e⟩⟩ := _root_.DerivedCategory.Plus.exists_injective_nonempty_iso N n
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
  let P := (HomotopyCategory.Plus.quotient _).obj M
  have : IsIso ((v)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) := by
    dsimp only [P, M]
    infer_instance
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).isIso_derivedPlus_counit_app_Qh_obj
    (fun Y ↦ inferInstance) P
  exact (NatTrans.isIso_app_iff_of_iso _
    ((_root_.DerivedCategory.Plus.quotientCompQhIso _).app M ≪≫ e)).1 this

/-- For an open immersion `v`, the pullback `v^*` of the unit `K ⟶ Rv_* v^* K` is an
isomorphism, by the triangle identity. -/
instance isIso_mapDerivedCategoryPlus_map_derivedPlus_unit_app {V X : Scheme.{u}} (v : V ⟶ X)
    [IsOpenImmersion v]
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).derivedPlus.unit.app K)) := by
  have h :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).derivedPlus.left_triangle_components K
  rw [← IsIso.eq_comp_inv] at h
  rw [h, Category.id_comp]
  infer_instance

/-- **The cone of the unit is supported on the closed complement**: for an open immersion `v` with
closed complement `i` and a distinguished triangle `K ⟶ Rv_* v^* K ⟶ Δ ⟶ K[1]` whose first map
is the unit, `Δ ≅ Ri_* i^* Δ`. -/
theorem nonempty_iso_rightDerivedLowerStarPlus_of_distTriang_unit {V W X : Scheme.{u}}
    (v : V ⟶ X) [IsOpenImmersion v] (i : W ⟶ X) [IsClosedImmersion i]
    (hvi : Set.range i.base = (Set.range v.base)ᶜ)
    {K Δ : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (w₂ : (v)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
      (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) ⟶ Δ) (w₃ : Δ ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).derivedPlus.unit.app
      K) w₂ w₃ ∈ distTriang _) :
    Nonempty (Δ ≅ (i)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
      (((i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj Δ)) := by
  -- `v^* Δ = 0`
  have hv : IsZero (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj Δ) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus).map_distinguished _ hT)).2
      (isIso_mapDerivedCategoryPlus_map_derivedPlus_unit_app v K)
  -- the open–closed triangle `v_! v^* Δ ⟶ Δ ⟶ Ri_* i^* Δ ⟶`
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) v i hvi
    (_root_.DerivedCategory.Plus.ι.obj Δ)
  have : IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
      (_root_.DerivedCategory.Plus.ι.obj Δ)) :=
    (Triangle.isZero₁_iff_isIso₂ _ hw).1 (Functor.map_isZero _
      (_root_.DerivedCategory.Plus.ι.map_isZero hv))
  exact ⟨_root_.DerivedCategory.Plus.ι.preimageIso
    (asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
      (_root_.DerivedCategory.Plus.ι.obj Δ)) ≪≫
      ((i)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app
        (((i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj Δ)).symm)⟩

/-- **The open–closed dévissage**: let `v : V ⟶ X` be an open immersion with closed complement
`i : W ⟶ X`, `j : X ⟶ Y` a morphism of `S`-schemes with `X` locally of finite type over `S`, and
`K ⟶ Rv_* v^* K ⟶ Δ ⟶ K[1]` a distinguished triangle whose first map is the unit. If the direct
images of `v^* K` along `v` and `v ≫ j` and the direct image of the bounded constructible complex
`i^* Δ` along `i ≫ j` are bounded constructible and commute with base change over `U`, then so is
the direct image of `K` along `j`. -/
theorem HasDirectImageBaseChangeOnPlus.of_distTriang_unit [Finite Λ] {S V W X Y : Scheme.{u}}
    {fY : Y ⟶ S}
    (j : X ⟶ Y) [LocallyOfFiniteType (j ≫ fY)] (v : V ⟶ X) [IsOpenImmersion v] (i : W ⟶ X)
    [IsClosedImmersion i] (hvi : Set.range i.base = (Set.range v.base)ᶜ)
    {K Δ : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (w₂ : (v)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
      (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) ⟶ Δ) (w₃ : Δ ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).derivedPlus.unit.app
      K) w₂ w₃ ∈ distTriang _) {U : Set S}
    (hv : HasDirectImageBaseChangeOnPlus Λ (j ≫ fY) v
      (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) U)
    (hjv : HasDirectImageBaseChangeOnPlus Λ fY (v ≫ j)
      (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) U)
    (hΔ : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) W
      (_root_.DerivedCategory.Plus.ι.obj
        (((i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj Δ)))
    (hW : HasDirectImageBaseChangeOnPlus Λ fY (i ≫ j)
      (((i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj Δ) U) :
    HasDirectImageBaseChangeOnPlus Λ fY j K U := by
  have h₂ := HasDirectImageBaseChangeOnPlus.of_comp v j hv hjv
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStarPlus_of_distTriang_unit v i hvi w₂ w₃ hT
  have h₃ : HasDirectImageBaseChangeOnPlus Λ fY j Δ U :=
    (HasDirectImageBaseChangeOnPlus.of_comp i j
      (hasDirectImageBaseChangeOnPlus_of_isClosedImmersion (fX := j ≫ fY) i hΔ U) hW).of_iso
      e.symm
  exact HasDirectImageBaseChangeOnPlus.of_distTriang₁ hT h₂ h₃

end Etale

end AlgebraicGeometry
