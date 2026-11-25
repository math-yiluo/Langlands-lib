/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic

/-!

# The pullback of `L ⊠ K` to the strictly local model is an extension by zero

Blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (i): in the strictly local model
`AlgebraicGeometry.Etale.CurveLocalModel`, if `Ly^* K = 0` then `P = Lτ^*(L ⊠ K)` vanishes on
the horizontal axis `H = X × {y}` of `T`, so that `P` is the extension by zero of its
restriction to `T ∖ H`.

## Main results

- `AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app`:
  **extension-by-zero criterion.** For an open immersion `j` and a closed immersion `i` with
  complementary ranges, if `Li^* F = 0` then the counit `j_! j^* F ⟶ F` is an isomorphism.
- `AlgebraicGeometry.Etale.\
  isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app_of_forall`: the same
  criterion, with the vanishing tested at geometric points outside `j`.
- `AlgebraicGeometry.Etale.CurveLocalModel.isZero_leftDerivedUpperStar_hH_obj`: `P` vanishes
  on `H`.
- `AlgebraicGeometry.Etale.CurveLocalModel.isIso_counit_app_openComplement_hH`: `P` is the
  extension by zero of its restriction to `T ∖ H`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Criterion

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {W Z : Scheme.{u}} (j : W ⟶ Z) [IsOpenImmersion j]

/-- The restriction `D(j^*)` inverts the counit of the derived adjunction `D(j_!) ⊣ D(j^*)`
along an open immersion, by the triangle identity since the unit is invertible. -/
instance isIso_mapDerivedCategory_upperStar_map_derivedOpenImmersionAdjunction_counit_app
    (F : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsIso (D((j)^*[A]).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app F)) := by
  have h := (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := h.full
  have := h.faithful
  infer_instance

/-- **Extension-by-zero criterion.** Let `j : W ⟶ Z` be an open immersion and `i : Y ⟶ Z` a
closed immersion with complementary ranges. If `Li^* F = 0`, then the counit
`j_! j^* F ⟶ F` of the derived adjunction `D(j_!) ⊣ D(j^*)` is an isomorphism, i.e. `F` is the
extension by zero of its restriction to `W`. -/
theorem isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app
    {Y : Scheme.{u}} (i : Y ⟶ Z) [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (F : DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hF : IsZero ((L((i)^*[A])).obj F)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app F) := by
  refine (jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar' A j i hij).isIso_of_pairFunctor
    _ inferInstance ?_
  refine isIso_of_source_target_iso_zero _ ?_ ?_
  · exact (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range A j i
      (by rw [hij]; exact disjoint_compl_left) _).isoZero
  · exact (hF.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory A i).app F).symm).isoZero

/-- `F` is isomorphic to the extension by zero `j_! j^* F` of its restriction to `W` as soon as
`Li^* F = 0` for a closed immersion `i` with range the complement of that of `j`. -/
lemma nonempty_iso_openImmersionLowerShriek_obj_of_isZero
    {Y : Scheme.{u}} (i : Y ⟶ Z) [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (F : DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (hF : IsZero ((L((i)^*[A])).obj F)) :
    Nonempty (F ≅ D((j)_!open[A]).obj (D((j)^*[A]).obj F)) :=
  have := isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app A j i hij F hF
  ⟨(asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app F)).symm⟩

end Criterion

section Points

variable {Λ : Type (u + 1)} [CommRing Λ] {W Z : Scheme.{u}} (j : W ⟶ Z) [IsOpenImmersion j]

/-- **Extension-by-zero criterion, pointwise.** For an open immersion `j : W ⟶ Z`, if the
derived stalk `Ls^* F` vanishes at every geometric point `s` of `Z` outside `W`, then the
counit `j_! j^* F ⟶ F` is an isomorphism. -/
theorem isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app_of_forall
    (F : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z),
      s.base (IsLocalRing.closedPoint Ω) ∉ Set.range j.base →
        IsZero ((L((s)^*[ModuleCat.{u + 1} Λ])).obj F)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) j).counit.app F) := by
  rw [isIso_iff_forall_isIso_leftDerivedUpperStar_map]
  intro Ω _ _ s
  by_cases hs : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range j.base
  · have hr : Set.range s.base ⊆ Set.range j.base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]
    rw [NatIso.isIso_map_iff (leftDerivedUpperStarComp _ (IsOpenImmersion.lift j s hr) j s
      (IsOpenImmersion.lift_fac j s hr).symm), Functor.comp_map]
    have := (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).counit.app F)).1 inferInstance
    infer_instance
  · refine isIso_of_source_target_iso_zero _ ?_ (hF Ω s hs).isoZero
    exact
      (isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
      _ j s (by
        rw [Set.disjoint_left]
        rintro _ ⟨p, rfl⟩
        rwa [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]) _).isoZero

end Points

namespace CurveLocalModel

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

variable {Λ : Type (u + 1)} [CommRing Λ]

omit [IsAlgClosed k] in
/-- For a morphism `g : S ⟶ X ×_k X` whose second coordinate factors through `y` and
`Ly^* K = 0`, the pullback `Lg^*(L ⊠ K) ≅ Lg^*Lp₁^*L ⊗ᴸ Lq^*Ly^*K` vanishes. -/
lemma isZero_leftDerivedUpperStar_externalProduct_of_comp_snd_eq {S : Scheme.{u}}
    (g : S ⟶ pullback M.f M.f) (q : S ⟶ Spec (.of k)) (hg : g ≫ pullback.snd M.f M.f = q ≫ M.y)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsZero ((L((g)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :=
  (isZero_derivedTensor_obj_obj_of_isZero_right _
    (((L((q)^*[ModuleCat.{u + 1} Λ])).map_isZero hK).of_iso
      (((leftDerivedUpperStarComp _ g (pullback.snd M.f M.f)).app K).symm ≪≫
        (leftDerivedUpperStarComp _ q M.y (g ≫ pullback.snd M.f M.f) hg).app K))).of_iso
    (leftDerivedUpperStarTensorIso _ g _ _)

/-- `P = Lτ^*(L ⊠ K)` vanishes on the horizontal axis `H` of `T` when `Ly^* K = 0`. -/
lemma isZero_leftDerivedUpperStar_hH_obj
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsZero ((L((M.hH)^*[ModuleCat.{u + 1} Λ])).obj ((L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))) :=
  (M.isZero_leftDerivedUpperStar_externalProduct_of_comp_snd_eq (M.hH ≫ M.τ)
    (pullback.fst M.horizontal M.τ ≫ M.f)
    (by rw [Category.assoc, ← pullback.condition_assoc, horizontal_snd, Category.assoc])
    L K hK).of_iso
    ((leftDerivedUpperStarComp _ M.hH M.τ).app _).symm

lemma range_hH_eq_compl_range_ι :
    Set.range M.hH.base = (Set.range M.hH.openComplement.ι.base)ᶜ := by
  rw [Scheme.Opens.range_ι, Scheme.Hom.openComplement, TopologicalSpace.Opens.coe_mk,
    compl_compl]

/-- Blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (i): if `Ly^* K = 0`, then
`P = Lτ^*(L ⊠ K)` is the extension by zero of its restriction to `T ∖ H`: the counit
`j_! j^* P ⟶ P` along `j : T ∖ H ⟶ T` is an isomorphism. -/
theorem isIso_counit_app_openComplement_hH
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
      M.hH.openComplement.ι).counit.app ((L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
        (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))) :=
  isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit_app _ _ M.hH
    M.range_hH_eq_compl_range_ι _ (M.isZero_leftDerivedUpperStar_hH_obj L K hK)

/-- Blueprint `lemma-vanishing-local-term-zero-stalk--1`, item (i): if `Ly^* K = 0`, then
`P = Lτ^*(L ⊠ K)` is isomorphic to the extension by zero of its restriction to `T ∖ H`. -/
theorem nonempty_iso_openImmersionLowerShriek_openComplement_hH
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    Nonempty ((L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
        (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K) ≅
      D((M.hH.openComplement.ι)_!open[ModuleCat.{u + 1} Λ]).obj
        (D((M.hH.openComplement.ι)^*[ModuleCat.{u + 1} Λ]).obj
          ((L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
            (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)))) :=
  nonempty_iso_openImmersionLowerShriek_obj_of_isZero _ _ M.hH M.range_hH_eq_compl_range_ι _
    (M.isZero_leftDerivedUpperStar_hH_obj L K hK)

end CurveLocalModel

end AlgebraicGeometry.Etale
