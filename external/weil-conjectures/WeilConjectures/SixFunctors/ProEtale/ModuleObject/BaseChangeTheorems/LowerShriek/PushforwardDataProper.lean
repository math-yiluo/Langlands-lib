/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataCoherence

/-!
# The compact-support base change of a pushforward datum for proper morphisms

Let `P` be a pushforward datum for a coefficient ring `Λ`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`) whose comparisons along proper
refinements are isomorphisms (`hP : P.IsIsoRefinementPushforward`). For a proper `f`, the lower
shriek `Rf_!` of `P` is identified with the pushforward `Rf_*` of `P`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData.lowerShriekIsoLowerStar`), through
the trivial compactification `X ⟶[𝟙] X ⟶[f] Y`.

For a cartesian square `sq : IsPullback g' f' f g` with `f` and `f'` proper, the compact-support
base change `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` of `P` is, through these identifications, the
base change morphism `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of `P`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData.lowerShriekBaseChange_of_isProper`),
i.e. the mate of the pullback square comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` under the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`
(`BoundedConstructiblePushforwardData.lowerShriekBaseChange_of_isProper_mateEquiv`).
The proof is the one for the coefficient ring `ℚ̲̄_ℓ` (the file `BaseChangeProper` of this
directory), in the exchange formalism of `P`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section IsProperIso

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The adjunction `(𝟙 U)_! ⊣ L(𝟙 U)^*` on bounded constructible complexes attached to the
compactification `U ⟶[𝟙] U ⟶[j] X` of a proper `j` is identified with the identity adjunction by
`(𝟙 U)_! ≅ 𝟭` and `L(𝟙 U)^* ≅ 𝟭`: `ι⁻¹ ≫ ε = u` on `L(𝟙 U)^*`, for any coefficient ring `Λ`. -/
lemma boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_adjunction_counit
    (j : U ⟶ X) [IsProper j.left] (W : Dᵇc(U.left)⟦Λ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ ℓ j).inv.app
        ((boundedConstructibleUpperStar Λ ℓ (Compactification.ofIsProper j.left).overI).obj W) ≫
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ
        (Compactification.ofIsProper j.left).overI).counit.app W =
      (boundedConstructibleUpperStarId Λ ℓ U).hom.app W := by
  ext1
  have h := (Adjunction.map_restrictFullyFaithful_counit_app
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction _
        (Compactification.ofIsProper j.left).overI.left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _
          (Compactification.ofIsProper j.left).overI.left).symm)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ
        (Compactification.ofIsProper j.left).overI).symm
      (boundedConstructibleUpperStarCompatibility _ ℓ
        (Compactification.ofIsProper j.left).overI).symm W)
  have h1 (V : Dᵇc(U.left)⟦Λ⟧) :
      ((boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ ℓ j).inv.app V).hom =
        (derivedOpenImmersionLowerShriekId Λ U.left).inv.app V.obj := by
    simp only [Functor.id_obj, boundedConstructibleOpenImmersionLowerShriekOfIsProperIso,
      Functor.whiskeringRight_obj_obj, boundedConstructibleOpenImmersionLowerShriekCompatibility,
      ObjectProperty.liftCompιIso, Functor.FullyFaithful.preimageIso_inv, Iso.trans_inv,
      Iso.refl_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.id_app, Functor.comp_obj,
      ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
      Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
      Category.id_comp, ObjectProperty.homMk_hom]
    exact Category.comp_id _
  rw [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarId_hom_app_hom]
  have h' : ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ
      (Compactification.ofIsProper j.left).overI).counit.app W).hom =
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction _
        (Compactification.ofIsProper j.left).overI.left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion _
          (Compactification.ofIsProper j.left).overI.left).symm).counit.app W.obj := by
    refine h.trans ?_
    simp only [boundedConstructibleOpenImmersionLowerShriekCompatibility,
      boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso, Iso.symm_inv,
      Iso.refl_hom, NatTrans.id_app]
    exact id_comp_map_id_comp _ _ _
  have h2 := derivedOpenImmersionLowerShriekId_inv_app_comp_counit Λ U.left W.obj
  erw [h1, h']
  exact h2

end IsProperIso

namespace BoundedConstructiblePushforwardData

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (P : BoundedConstructiblePushforwardData Λ ℓ k)

/-- The exchange formalism of the pushforward datum `P`. -/
local notation "𝔽" => exchangeFormalism P

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The isomorphism `(𝟙 X)_! ≅ 𝟭` of the trivial compactification `X ⟶[𝟙] X ⟶[f] Y` of a proper
`f` is the identity isomorphism of the extension by zero of the exchange formalism of `P`, at the
middle object of the compactification. -/
lemma boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId (f : X ⟶ Y)
    [IsProper f.left] :
    boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ ℓ f =
      (𝔽).shId (SepFinType.mk (Compactification.ofIsProper f.left).overObj) :=
  Adjunction.iso_ext_of_inv_app_comp_counit
    ((𝔽).shAdj (𝟙 (SepFinType.mk (Compactification.ofIsProper f.left).overObj)))
    ((𝔽).pbId (SepFinType.mk (Compactification.ofIsProper f.left).overObj)) _ _
    (fun W ↦
      boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_adjunction_counit
      Λ ℓ f W)
    (fun W ↦ (𝔽).shId_inv_app_comp_counit _ W)

/-- The lower shriek `Rf_!^c` of `P` attached to the trivial compactification
`c = (X ⟶[𝟙] X ⟶[f] Y)` of a proper `f` is the pushforward along the proper map `X ⟶[f] Y` of
`c`. -/
noncomputable def lowerShriekOfCompactificationOfIsProperIso (f : X ⟶ Y) [IsProper f.left] :
    P.lowerShriekOfCompactification (Compactification.ofIsProper f.left) ≅
      P.lowerStar (X := (Compactification.ofIsProper f.left).overObj)
        (Compactification.ofIsProper f.left).overG :=
  Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso Λ ℓ f) _ ≪≫
    Functor.leftUnitor _

variable {P} in
/-- The isomorphism `Rf_! ≅ Rf_*` of `P` for a proper `f`: by independence of the
compactification, `Rf_!` is `Rf_!^c` for the trivial compactification `c = (X ⟶[𝟙] X ⟶[f] Y)`,
which is the pushforward along the proper map `X ⟶[f] Y` of `c`. (The pushforward is taken along
`(Compactification.ofIsProper f.left).overG`, which is `f` up to the identification of the
structure morphism of `X` with `f ≫ Y.hom`; for the `ℓ`-adic coefficient rings it is
definitionally the pushforward along `f`.) -/
noncomputable def lowerShriekIsoLowerStar (hP : P.IsIsoRefinementPushforward) (f : X ⟶ Y)
    [IsProper f.left] :
    P.lowerShriekOfCompactification (compactificationOverField f) ≅
      P.lowerStar (X := (Compactification.ofIsProper f.left).overObj)
        (Compactification.ofIsProper f.left).overG :=
  lowerShriekOfCompactificationIso hP (compactificationOverField f)
      (Compactification.ofIsProper f.left) ≪≫
    P.lowerShriekOfCompactificationOfIsProperIso f

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper f.left]
  [IsProper f'.left]

/-- The compact-support exchange map of `P` of the trivial compactifications of the proper `f`
and `f'` is the compact-support exchange map of the factorizations `Z ⟶[𝟙] Z ⟶[f] Y` and
`Z' ⟶[𝟙] Z' ⟶[f'] Y'` in the exchange formalism of `P`, where `Z` and `Z'` are the middle objects
of the compactifications. -/
lemma lowerShriekOfCompactificationBaseChange_ofIsProper_eq (sq : IsPullback g' f' f g)
    (hw : SepFinType.homMk (ofIsProperBaseChangeHom sq) ≫
        𝟙 (SepFinType.mk (Compactification.ofIsProper f.left).overObj) =
      𝟙 (SepFinType.mk (Compactification.ofIsProper f'.left).overObj) ≫
        SepFinType.homMk (ofIsProperBaseChangeHom sq))
    [IsIso ((𝔽).baseChange (SepFinType.homMk (ofIsProperBaseChangeHom sq))
      (𝟙 (SepFinType.mk (Compactification.ofIsProper f'.left).overObj))
      (𝟙 (SepFinType.mk (Compactification.ofIsProper f.left).overObj))
      (SepFinType.homMk (ofIsProperBaseChangeHom sq)) hw)] :
    P.lowerShriekOfCompactificationBaseChange (Compactification.ofIsProper f.left)
        (Compactification.ofIsProper f'.left) (ofIsProperBaseChangeHom sq)
        (isPullback_ofIsProper_overI sq) (isPullback_ofIsProper_overG sq) =
      ((𝔽).shriekBaseChange (𝟙 (SepFinType.mk (Compactification.ofIsProper f.left).overObj))
        (SepFinType.homMk (Compactification.ofIsProper f.left).overG)
        (𝟙 (SepFinType.mk (Compactification.ofIsProper f'.left).overObj))
        (SepFinType.homMk (Compactification.ofIsProper f'.left).overG)
        (SepFinType.homMk (ofIsProperBaseChangeHom sq))
        (SepFinType.homMk (ofIsProperBaseChangeHom sq)) (SepFinType.homMk g) hw
        (SepFinType.homMk_comp_homMk (isPullback_ofIsProper_overG sq).w)) := by
  obtain ⟨Xl, ⟨⟨⟩⟩, Xh⟩ := X
  obtain ⟨Xl', ⟨⟨⟩⟩, Xh'⟩ := X'
  obtain ⟨fl, ⟨⟨⟨⟩⟩⟩, fw⟩ := f
  obtain ⟨fl', ⟨⟨⟨⟩⟩⟩, fw'⟩ := f'
  change Xl ⟶ Y.left at fl
  change Xl' ⟶ Y'.left at fl'
  obtain rfl : Xh = fl ≫ Y.hom := by simpa using fw.symm
  obtain rfl : Xh' = fl' ≫ Y'.hom := by simpa using fw'.symm
  rfl

/-- The compact-support exchange map of `P` of the trivial compactifications of the proper `f`
and `f'` is the base change `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of `P` of the square of their
proper maps, through `Rf_!^c ≅ Rf_*`. -/
lemma lowerShriekOfCompactificationBaseChange_ofIsProper (sq : IsPullback g' f' f g) :
    P.lowerShriekOfCompactificationBaseChange (Compactification.ofIsProper f.left)
        (Compactification.ofIsProper f'.left) (ofIsProperBaseChangeHom sq)
        (isPullback_ofIsProper_overI sq) (isPullback_ofIsProper_overG sq) ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
        (P.lowerShriekOfCompactificationOfIsProperIso f').hom =
    Functor.whiskerRight (P.lowerShriekOfCompactificationOfIsProperIso f).hom
        (boundedConstructibleUpperStar Λ ℓ g) ≫
      P.baseChange (isPullback_ofIsProper_overG sq).toCommSq := by
  have hw : SepFinType.homMk (ofIsProperBaseChangeHom sq) ≫
        𝟙 (SepFinType.mk (Compactification.ofIsProper f.left).overObj) =
      𝟙 (SepFinType.mk (Compactification.ofIsProper f'.left).overObj) ≫
        SepFinType.homMk (ofIsProperBaseChangeHom sq) := by
    rw [Category.comp_id, Category.id_comp]
  have : IsIso ((𝔽).baseChange (SepFinType.homMk (ofIsProperBaseChangeHom sq))
      (𝟙 (SepFinType.mk (Compactification.ofIsProper f'.left).overObj))
      (𝟙 (SepFinType.mk (Compactification.ofIsProper f.left).overObj))
      (SepFinType.homMk (ofIsProperBaseChangeHom sq)) hw) :=
    P.isIso_baseChange_exchangeFormalism (IsPullback.of_id_snd (f := ofIsProperBaseChangeHom sq))
  have key := (𝔽).shriekBaseChange_id_left
    (SepFinType.homMk (Compactification.ofIsProper f.left).overG)
    (SepFinType.homMk (Compactification.ofIsProper f'.left).overG)
    (SepFinType.homMk (ofIsProperBaseChangeHom sq)) (SepFinType.homMk g) hw
    (SepFinType.homMk_comp_homMk (isPullback_ofIsProper_overG sq).w)
  simp only [lowerShriekOfCompactificationOfIsProperIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom,
    P.boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId]
  rewrite [P.baseChange_eq_pfBaseChange,
    P.lowerShriekOfCompactificationBaseChange_ofIsProper_eq sq hw]
  -- Compare components so the pullback identification is checked on objects and morphisms.
  refine NatTrans.ext (funext fun K ↦ ?_)
  exact congr_app key K

variable {P}

/-- **`Ex_!` of `P` for proper vertical maps is `Ex_*`**: under the identifications
`Rf_! ≅ Rf_*` and `Rf'_! ≅ Rf'_*` (`lowerShriekIsoLowerStar`), the compact-support base change
of a cartesian square with `f` and `f'` proper is the base change morphism `Ex_*` of `P`. -/
theorem lowerShriekBaseChange_of_isProper (hP : P.IsIsoRefinementPushforward)
    (sq : IsPullback g' f' f g) :
    lowerShriekBaseChange hP sq ≫
        Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
          (lowerShriekIsoLowerStar hP f').hom =
      Functor.whiskerRight (lowerShriekIsoLowerStar hP f).hom
          (boundedConstructibleUpperStar Λ ℓ g) ≫
        P.baseChange (isPullback_ofIsProper_overG sq).toCommSq := by
  rw [lowerShriekBaseChange_eq_baseChange hP sq (Compactification.ofIsProper f.left)
      (Compactification.ofIsProper f'.left) (ofIsProperBaseChangeHom sq)
      (isPullback_ofIsProper_overI sq) (isPullback_ofIsProper_overG sq)]
  have hc : Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
      (lowerShriekOfCompactificationIso hP (Compactification.ofIsProper f'.left)
        (compactificationOverField f')).hom ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
      (lowerShriekOfCompactificationIso hP (compactificationOverField f')
        (Compactification.ofIsProper f'.left)).hom = 𝟙 _ := by
    rw [← Functor.whiskerLeft_comp, ← Iso.trans_hom, lowerShriekOfCompactificationIso_trans,
      lowerShriekOfCompactificationIso_refl]
    simp
  simp only [lowerShriekIsoLowerStar, Iso.trans_hom, Functor.whiskerLeft_comp,
    Functor.whiskerRight_comp, Category.assoc]
  rw [reassoc_of% hc, P.lowerShriekOfCompactificationBaseChange_ofIsProper sq]

/-- **`Ex_!` of `P` for proper vertical maps is the mate of the pullback square comparison**:
under the identifications `κ_f : Rf_! ≅ Rf_*` and `κ_{f'} : Rf'_! ≅ Rf'_*`
(`lowerShriekIsoLowerStar`), the compact-support base change `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!`
of a cartesian square with `f` and `f'` proper is the mate `Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of the
pullback square comparison `θ : Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` under the adjunctions
`Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`: `κ_f ≫ mate(θ) = Ex_! ≫ κ_{f'}`. -/
theorem lowerShriekBaseChange_of_isProper_mateEquiv (hP : P.IsIsoRefinementPushforward)
    (sq : IsPullback g' f' f g) :
    Functor.whiskerRight (lowerShriekIsoLowerStar hP f).hom
        (boundedConstructibleUpperStar Λ ℓ g) ≫
      (mateEquiv (P.adj (Compactification.ofIsProper f.left).overG)
        (P.adj (Compactification.ofIsProper f'.left).overG)
        (boundedConstructiblePullbackSquareComparison Λ ℓ
          (isPullback_ofIsProper_overG sq).toCommSq).hom) =
    lowerShriekBaseChange hP sq ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar Λ ℓ g')
        (lowerShriekIsoLowerStar hP f').hom := by
  rw [lowerShriekBaseChange_of_isProper hP sq, baseChange, Adjunction.exchangeRight_eq_mateEquiv]

end BoundedConstructiblePushforwardData

end AlgebraicGeometry.ProEtale.CondensedRing
