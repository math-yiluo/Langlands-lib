/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModule
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.BraidingShift
public import WeilConjectures.CategoryTheory.Monoidal.BraidingSelfTrivial
public import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineKernelAssembly

/-!
# The self-braiding of the shifted Tate twists

The Koszul braiding of `D(X_ét, Λ)` is trivial on `Λ_X(m) ⊗ᴸ Λ_X(m)`, and on
`Λ_X(m)[n] ⊗ᴸ Λ_X(m)[n]` for even `n`, as well as on all their derived pullbacks. This is the
hypothesis on the braiding of `La^* Lq^* τ` in
`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class`.

* `Λ_X(m) ⊗ᴸ Λ_X(m) ≅ Λ_X(2m)` is a sheaf placed in degree zero, so its endomorphisms are
  determined at the geometric points
  (`AlgebraicGeometry.Etale.hom_ext_of_leftDerivedUpperStar_map_eq`).
  The derived pullback is braided, and at a geometric point `x : Spec Ω ⟶ X` the twist is
  trivial, `Lx^* Λ_X(m) ≅ Λ_{Spec Ω}(m) ≅ Λ`, whose self-braiding is the identity
  (`AlgebraicGeometry.Etale.braiding_tateObject_self`).
* The braiding of `K[n] ⊗ᴸ K[n]` is the shift of the braiding of `K ⊗ᴸ K` with the sign
  `(-1) ^ (n * n)` (`CategoryTheory.MonoidalCategory.braiding_shift_self_eq_id`).
* Braided functors preserve trivial self-braidings
  (`CategoryTheory.Functor.braiding_obj_self_eq_id`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- The same instance context as `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.
-- ProjectiveLineKernelAssembly`, so that the statements specialise syntactically.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

attribute [local instance] leftDerivedUpperStarMonoidal _root_.DerivedCategory.braidedCategory'

section TateTwist

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

/-- Over a separably closed field, the Tate twists are trivial: `Λ_{Spec Ω}(m) ≅ Λ`. -/
lemma nonempty_tateObject_iso_tensorUnit_of_isSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [HasInvertibleExponent Λ (Spec (.of Ω))] (m : ℤ) :
    Nonempty (tateObject Λ (Spec (.of Ω)) m ≅ 𝟙_ (DerivedCategoryModule Λ (Spec (.of Ω)))) := by
  obtain ⟨L, -, hL, ⟨e⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) (Spec (.of Ω)) m
  obtain ⟨f⟩ := hL Ω (𝟙 _)
  obtain ⟨g⟩ := Scheme.nonempty_iso_constantSheaf_of_sheafFiber_iso L f
  exact ⟨e ≪≫ (_root_.DerivedCategory.singleFunctor _ 0).mapIso g ≪≫
    (unitIsoSingleFunctorConstantSheaf Λ _).symm⟩

/-- **The self-braiding of a Tate twist is trivial.** The braiding of `Λ_X(m) ⊗ᴸ Λ_X(m)` is the
identity: this object is the sheaf `Λ_X(2m)` placed in degree zero, so it suffices to check it
at the geometric points, where the twist is trivial. -/
theorem braiding_tateObject_self (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m : ℤ) :
    (β_ (tateObject Λ X m) (tateObject Λ X m)).hom = 𝟙 _ := by
  obtain ⟨L, -, -, ⟨e⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) X (m + m)
  refine hom_ext_of_leftDerivedUpperStar_map_eq (HasTateTwist.twistObjectAddIso X m m ≪≫ e)
    (HasTateTwist.twistObjectAddIso X m m ≪≫ e) fun Ω _ _ x ↦ ?_
  have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
  let := leftDerivedUpperStarBraidedModuleCat Λ x
  obtain ⟨t⟩ := nonempty_tateObject_iso_tensorUnit_of_isSepClosed Λ Ω m
  exact ((Functor.braiding_obj_self_eq_id_iff _ _).1 (braiding_self_eq_id_of_iso_tensorUnit
    (HasTateTwist.leftDerivedUpperStarTwistObjectIso x m ≪≫ t))).trans
      (CategoryTheory.Functor.map_id _ _).symm

/-- The self-braiding of an even shift `Λ_X(m)[n]` of a Tate twist is trivial. -/
theorem braiding_shift_tateObject_self (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m : ℤ)
    {n : ℤ} (hn : Even n) :
    (β_ ((tateObject Λ X m)⟦n⟧) ((tateObject Λ X m)⟦n⟧)).hom = 𝟙 _ :=
  braiding_shift_self_eq_id
    (fun _ _ _ ↦ _root_.DerivedCategory.braiding_hom_commShiftIso_hom_app _ _ _)
    (_root_.DerivedCategory.braiding_hom_braiding_hom _ fun _ _ ↦ SymmetricCategory.symmetry _ _)
    (braiding_tateObject_self Λ X m) hn

/-- **The self-braiding of a pulled back shifted Tate twist is trivial.** For `f : Y ⟶ S`,
`g : Z ⟶ Y` and even `n`, the braiding of `Lg^* Lf^* (Λ_S(m)[n])` with itself is the identity.
For `f = q : ℙ¹_S ⟶ S`, `g = a : ℙ¹_{ℙ¹_S} ⟶ ℙ¹_S`, `m = 1` and `n = 2` this is the hypothesis
`hsymm` of `AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class`. -/
theorem braiding_leftDerivedUpperStar_shift_tateObject_self {Z Y S : Scheme.{u}} (g : Z ⟶ Y)
    (f : Y ⟶ S) [HasInvertibleExponent Λ S] (m : ℤ) {n : ℤ} (hn : Even n) :
    (β_ ((L((g)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ S m)⟦n⟧)))
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ S m)⟦n⟧)))).hom = 𝟙 _ := by
  let := leftDerivedUpperStarBraidedModuleCat Λ f
  let := leftDerivedUpperStarBraidedModuleCat Λ g
  exact Functor.braiding_obj_self_eq_id _
    (Functor.braiding_obj_self_eq_id _ (braiding_shift_tateObject_self Λ S m hn))

end TateTwist

section ProjectiveLine

variable (Λ : Type (u + 1)) [CommRing Λ] [HasKummerClass Λ] (S : Scheme.{u})
  [HasInvertibleExponent Λ S]

/-- The hypothesis `hsymm` of `AlgebraicGeometry.Etale.exists_projectiveLineAdjunction_of_class`:
for `P = ℙ¹_S`, `W = ℙ¹_P` and `τ = Λ_S(1)[2]`, the braiding of `La^* Lq^* τ` with itself is the
identity. -/
theorem braiding_projectiveLineKernelObject_self :
    (β_ ((L(((ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
          ℙ(Option (ULift.{u} (Fin 1)); S)))^*[ModuleCat.{u + 1} Λ])).obj
        ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj
          ((tateObject Λ S 1)⟦(2 : ℤ)⟧)))
      ((L(((ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
          ℙ(Option (ULift.{u} (Fin 1)); S)))^*[ModuleCat.{u + 1} Λ])).obj
        ((L(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj
          ((tateObject Λ S 1)⟦(2 : ℤ)⟧)))).hom = 𝟙 _ :=
  braiding_leftDerivedUpperStar_shift_tateObject_self Λ _ _ 1 even_two

end ProjectiveLine

end Etale

end AlgebraicGeometry
