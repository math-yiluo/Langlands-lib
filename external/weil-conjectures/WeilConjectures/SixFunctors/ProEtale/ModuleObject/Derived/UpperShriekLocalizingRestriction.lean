/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureRepresentable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing

/-!
# The exceptional inverse image on `Loc(Dᵇc)` restricts to `Dᵇc`

Let `Λ` be a commutative condensed ring and `c = (X ⟶[j] X̄ ⟶[p] Y)` a compactification of
`f : X ⟶ Y` such that `Rf_!(c)⟦Λ⟧` has the properties `LowerShriekLocalizingHypotheses` of blueprint
`proposition-construction-independence-rf-shriek`; in particular it maps `Dᵇc(X)⟦Λ⟧` into
`Dᵇc(Y)⟦Λ⟧`, and so restricts to a functor `Rf_!(c) : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekBoundedConstructible`).

If this restriction has a right adjoint, then every right adjoint `f^!` of
`Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` maps `Dᵇc(Y)⟦Λ⟧` into `Dᵇc(X)⟦Λ⟧`
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint`):
for `N ∈ Dᵇc(Y)⟦Λ⟧`, the value `f^!_b N` of the right adjoint on `Dᵇc` represents
`A ↦ Hom(Rf_! A, N)` on `Dᵇc(X)⟦Λ⟧`, and the objects of `Dᵇc(X)⟦Λ⟧` detect isomorphisms of
`Loc(Dᵇc(X)⟦Λ⟧)` (`CategoryTheory.ObjectProperty.isIso_homEquiv_of_bijective_localizingClosure`),
so `f^! N ≅ f^!_b N`. This is the last step of the proofs of blueprints
`theorem-f-shriek-ell-adic-coefficients` and `sk-thm-int-restriction`, with the existence of the
right adjoint on `Dᵇc` as input.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The compact-support direct image `Rf_!(c) : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible
complexes, for a compactification `c` with the properties of blueprint
`proposition-construction-independence-rf-shriek`: the restriction of `Rf_!(c)⟦Λ⟧`. -/
noncomputable abbrev rightDerivedLowerShriekBoundedConstructible
    (hc : LowerShriekLocalizingHypotheses Λ c) :
    (boundedConstructible (condensedRingObj Λ X)).FullSubcategory ⥤
      (boundedConstructible (condensedRingObj Λ Y)).FullSubcategory :=
  (boundedConstructible (condensedRingObj Λ Y)).lift
    ((boundedConstructible _).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)
    fun K ↦ hc.2.1 K.obj K.2

omit [IsCommMonObj Λ] in
/-- The compact-support direct image `Rf_!(c)` on bounded constructible complexes is a left
adjoint as soon as it is isomorphic, compatibly with the inclusions of `Dᵇc` into the derived
categories, to a left adjoint `F'`. -/
lemma isLeftAdjoint_rightDerivedLowerShriekBoundedConstructible_of_iso
    (hc : LowerShriekLocalizingHypotheses Λ c)
    {F' : (boundedConstructible (condensedRingObj Λ X)).FullSubcategory ⥤
      (boundedConstructible (condensedRingObj Λ Y)).FullSubcategory} [F'.IsLeftAdjoint]
    (e : F' ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c) :
    (rightDerivedLowerShriekBoundedConstructible hc).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (e ≪≫ (ObjectProperty.liftCompιIso _ _ _).symm))

omit [IsCommMonObj Λ] in
/-- If the compact-support direct image `Rf_!(c)` on bounded constructible complexes is a left
adjoint, then every right adjoint `f^!` of `Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` maps
`Dᵇc(Y)⟦Λ⟧` into `Dᵇc(X)⟦Λ⟧`: on such objects it agrees with the right adjoint on `Dᵇc`. -/
theorem boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint
    (hc : LowerShriekLocalizingHypotheses Λ c)
    [(rightDerivedLowerShriekBoundedConstructible hc).IsLeftAdjoint]
    {G : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X}
    (adj : rightDerivedLowerShriekLocalizing hc ⊣ G)
    (L : LocalizingBoundedConstructible Λ Y)
    (hL : boundedConstructible (condensedRingObj Λ Y) L.obj) :
    boundedConstructible (condensedRingObj Λ X) (G.obj L).obj := by
  let Fb := rightDerivedLowerShriekBoundedConstructible hc
  let adjb := Adjunction.ofIsLeftAdjoint Fb
  let Lb : (boundedConstructible (condensedRingObj Λ Y)).FullSubcategory := ⟨L.obj, hL⟩
  let Tb := Fb.rightAdjoint.obj Lb
  let T : LocalizingBoundedConstructible Λ X :=
    ⟨Tb.obj, ObjectProperty.le_localizingClosure _ _ Tb.2⟩
  let ε : (rightDerivedLowerShriekLocalizing hc).obj T ⟶ L :=
    ObjectProperty.homMk (adjb.counit.app Lb).hom
  have hε : ∀ A : LocalizingBoundedConstructible Λ X,
      ∀ hA : boundedConstructible (condensedRingObj Λ X) A.obj,
      (fun f : A ⟶ T ↦ (rightDerivedLowerShriekLocalizing hc).map f ≫ ε) =
        (fun g : Fb.obj ⟨A.obj, hA⟩ ⟶ Lb ↦ (ObjectProperty.homMk g.hom :
            (rightDerivedLowerShriekLocalizing hc).obj A ⟶ L)) ∘
          (adjb.homEquiv ⟨A.obj, hA⟩ Lb).symm ∘
            fun f : A ⟶ T ↦ (ObjectProperty.homMk f.hom : (⟨A.obj, hA⟩ :
              (boundedConstructible (condensedRingObj Λ X)).FullSubcategory) ⟶ Tb) := by
    intro A hA
    ext f
    simp [Adjunction.homEquiv_counit, Fb, ε, rightDerivedLowerShriekLocalizing,
      ObjectProperty.localizingClosureLift]
  have := ObjectProperty.isIso_homEquiv_of_bijective_localizingClosure adj ε fun A hA ↦ by
    rw [hε A hA]
    refine Function.Bijective.comp ?_ (Function.Bijective.comp (Equiv.bijective _) ?_)
    · exact ⟨fun g g' h ↦ by ext; simpa using congrArg (fun x ↦ x.hom) h,
        fun g ↦ ⟨ObjectProperty.homMk g.hom, rfl⟩⟩
    · exact ⟨fun g g' h ↦ by ext; simpa using congrArg (fun x ↦ x.hom) h,
        fun g ↦ ⟨ObjectProperty.homMk g.hom, rfl⟩⟩
  exact (boundedConstructible (condensedRingObj Λ X)).prop_of_iso
    ((ObjectProperty.ι _).mapIso (asIso (adj.homEquiv T L ε))) Tb.2

end AlgebraicGeometry.ProEtale.CondensedRing
