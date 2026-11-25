/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Restriction of scalars, pullbacks and base change maps

Let `φ : Λ →+* Λ'` be a morphism of rings. Restriction of scalars along `φ` commutes with the
direct image (`AlgebraicGeometry.Etale.lowerStarCompRestrictScalarsIso`) and with the derived
direct image (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`). This file
shows that it also commutes with pullbacks and with the base change map of a commutative square,
so that the base change map of a sheaf of `Λ'`-modules may be computed over `Λ`.

## Main statements

- `AlgebraicGeometry.Etale.upperStarRestrictScalars`: the comparison `f^* ∘ res ⟶ res ∘ f^*`,
  an isomorphism by `AlgebraicGeometry.Etale.isIso_upperStarRestrictScalars`.
- `AlgebraicGeometry.Etale.baseChangeMap_restrictScalars`: restriction of scalars commutes with
  the underived base change map of a commutative square.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`, for the unfolded
base change morphism. -/
instance isIso_rightDerivedFunctorPlusBaseChange_lowerStarCompRestrictScalarsIso
    {T S : Scheme.{u}} (g : T ⟶ S) :
    IsIso (Functor.rightDerivedFunctorPlusBaseChange (lowerStarCompRestrictScalarsIso φ g).hom) :=
  isIso_rightDerivedLowerStarRestrictScalars φ g

section UpperStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The mate of `AlgebraicGeometry.Etale.upperStarRestrictScalars` is the identification
`f_* ∘ res = res ∘ f_*`. -/
lemma mateEquiv_upperStarRestrictScalars :
    mateEquiv (upperStarLowerStarAdjunction _ f) (upperStarLowerStarAdjunction _ f)
      (upperStarRestrictScalars φ f) = (lowerStarCompRestrictScalarsIso φ f).hom :=
  Equiv.apply_symm_apply _ _

/-- The unit of `f^* ⊣ f_*` is compatible with restriction of scalars. -/
@[reassoc]
lemma restrictScalars_map_upperStarLowerStarAdjunction_unit_app
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((upperStarLowerStarAdjunction _ f).unit.app M) ≫
        (lowerStarCompRestrictScalarsIso φ f).hom.app _ =
      (upperStarLowerStarAdjunction _ f).unit.app _ ≫
        (f)_*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalars φ f).app M) :=
  unit_mateEquiv_symm (upperStarLowerStarAdjunction _ f)
    (upperStarLowerStarAdjunction _ f) (lowerStarCompRestrictScalarsIso φ f).hom M

/-- The counit of `f^* ⊣ f_*` is compatible with restriction of scalars. -/
@[reassoc]
lemma upperStarRestrictScalars_app_comp_counit
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarRestrictScalars φ f).app _ ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).map
          ((upperStarLowerStarAdjunction _ f).counit.app M) =
      (f)^*[ModuleCat.{u + 1} Λ].map ((lowerStarCompRestrictScalarsIso φ f).hom.app M) ≫
        (upperStarLowerStarAdjunction _ f).counit.app _ :=
  (mateEquiv_counit_symm (upperStarLowerStarAdjunction _ f)
    (upperStarLowerStarAdjunction _ f) (lowerStarCompRestrictScalarsIso φ f).hom M).symm

end UpperStar

section Comp

open TwoSquare

variable {Z W V : Scheme.{u}}

/-- The composition isomorphism `c^* ≅ b^* ⋙ a^*` is the conjugate of the composition
isomorphism of direct images. -/
lemma conjugateEquiv_upperStarComp_hom (A : Type (u + 1)) [CommRing A] (a : Z ⟶ W) (b : W ⟶ V)
    (c : Z ⟶ V) (hc : c = a ≫ b) :
    conjugateEquiv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b).comp
        (upperStarLowerStarAdjunction _ a)) (upperStarLowerStarAdjunction _ c)
        (upperStarComp _ a b c hc).hom =
      (lowerStarComp (ModuleCat.{u + 1} A) a b c hc).hom := by
  simp [upperStarComp]

/-- Restriction of scalars commutes with the composition isomorphisms of pullbacks: the
`2`-square `upperStarRestrictScalars φ c` along `c = a ≫ b` is the pasting of the
`2`-squares along `b` and `a`. -/
lemma upperStarRestrictScalars_comp (a : Z ⟶ W) (b : W ⟶ V) (c : Z ⟶ V) (hc : c = a ≫ b) :
    (upperStarRestrictScalars φ c).whiskerLeft (upperStarComp _ a b c hc).hom =
      (upperStarRestrictScalars φ b ≫ᵥ upperStarRestrictScalars φ a).whiskerRight
        (upperStarComp _ a b c hc).hom := by
  apply (mateEquiv ((upperStarLowerStarAdjunction _ b).comp (upperStarLowerStarAdjunction _ a))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c)).injective
  rw [conjugateEquiv_mateEquiv_vcomp _ (upperStarLowerStarAdjunction _ c),
    mateEquiv_conjugateEquiv_vcomp _
      ((upperStarLowerStarAdjunction _ b).comp (upperStarLowerStarAdjunction _ a)),
    mateEquiv_hcomp, mateEquiv_upperStarRestrictScalars, mateEquiv_upperStarRestrictScalars,
    mateEquiv_upperStarRestrictScalars, conjugateEquiv_upperStarComp_hom,
    conjugateEquiv_upperStarComp_hom]
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    lowerStarCompRestrictScalarsIso, Iso.refl_hom]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The components of `AlgebraicGeometry.Etale.upperStarRestrictScalars_comp`. -/
@[reassoc]
lemma upperStarRestrictScalars_comp_app (a : Z ⟶ W) (b : W ⟶ V) (c : Z ⟶ V) (hc : c = a ≫ b)
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarRestrictScalars φ c).app N ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).map
          ((upperStarComp _ a b c hc).hom.app N) =
      (upperStarComp _ a b c hc).hom.app _ ≫
        (a)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalars φ b).app N) ≫
        (upperStarRestrictScalars φ a).app _ := by
  have := congr_app (upperStarRestrictScalars_comp φ a b c hc) N
  simpa using this

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- Restriction of scalars commutes with the square isomorphism `p^* ⋙ h^* ≅ g^* ⋙ e^*` of a
commutative square. -/
@[reassoc]
lemma squareUpperStarIso_restrictScalars (sq : CommSq e h g p)
    (N : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app _ ≫
        (e)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalars φ g).app N) ≫
        (upperStarRestrictScalars φ e).app _ =
      (h)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalars φ p).app N) ≫
        (upperStarRestrictScalars φ h).app _ ≫
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
          ((squareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom.app N) := by
  have h₁ := upperStarRestrictScalars_comp_app φ e g (e ≫ g) rfl N
  have h₂ := upperStarRestrictScalars_comp_app φ h p (e ≫ g) sq.w N
  simp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← h₁, ← cancel_epi ((upperStarComp _ h p (e ≫ g) sq.w).hom.app _),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% h₂, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Restriction of scalars commutes with the underived base change map
`g_* ⋙ p^* ⟶ e^* ⋙ h_*` of a commutative square. -/
lemma baseChangeMap_restrictScalars (sq : CommSq e h g p)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (p)^*[ModuleCat.{u + 1} Λ].map ((lowerStarCompRestrictScalarsIso φ g).hom.app M) ≫
        (baseChangeMap (ModuleCat.{u + 1} Λ) sq).app _ ≫
        (h)_*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalars φ e).app M) =
      (upperStarRestrictScalars φ p).app _ ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).map
          ((baseChangeMap (ModuleCat.{u + 1} Λ') sq).app M) ≫
        (lowerStarCompRestrictScalarsIso φ h).hom.app _ := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality]
  have hc := mateEquiv_counit (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction _ h)
    (TwoSquare.mk _ _ _ _ (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom)
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj M)
  have hc' := mateEquiv_counit (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (upperStarLowerStarAdjunction _ h)
    (TwoSquare.mk _ _ _ _ (squareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom) M
  have hθ := (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.naturality
    ((lowerStarCompRestrictScalarsIso φ g).hom.app M)
  have hg := upperStarRestrictScalars_app_comp_counit φ g M
  have hh := upperStarRestrictScalars_app_comp_counit φ h
    ((e)^*[ModuleCat.{u + 1} Λ'].obj M)
  have hne := (upperStarRestrictScalars φ e).naturality
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g).counit.app M)
  have hnh := (upperStarRestrictScalars φ h).naturality
    ((baseChangeMap (ModuleCat.{u + 1} Λ') sq).app M)
  have hsq := squareUpperStarIso_restrictScalars_assoc φ sq
    ((g)_*[ModuleCat.{u + 1} Λ'].obj M)
    ((Sheaf.restrictScalars Y.smallEtaleTopology φ).map
      ((e)^*[ModuleCat.{u + 1} Λ'].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g).counit.app M)))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hne hnh hθ
  dsimp only [baseChangeMap, Functor.comp_obj] at hc hc' hnh ⊢
  rw [reassoc_of% hc, reassoc_of% hθ, ← CategoryTheory.Functor.map_comp_assoc, ← hg,
    CategoryTheory.Functor.map_comp, Category.assoc, hne, hsq, ← hh,
    reassoc_of% hnh, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (_ ≫ _ ≫ (Sheaf.restrictScalars Y.smallEtaleTopology φ).map ·) hc'.symm

end Comp

section Torsion

variable {X : Scheme.{u}}

/-- A sheaf of `Λ`-modules killed by `ϖ` is the restriction of scalars of a sheaf of
`Λ/ϖ`-modules: the counit `res (coext F) ⟶ F` of restriction and coextension of scalars along
`Λ ⟶ Λ/ϖ` is an isomorphism, as `Hom_Λ(Λ/ϖ, M) ⟶ M` is bijective when `ϖ M = 0`. -/
lemma isIso_restrictCoextendScalarsAdj_counit_app (ϖ : Λ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ (U : X.Etaleᵒᵖ) (x : F.obj.obj U), ϖ • x = 0) :
    IsIso ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {ϖ}))).counit.app F) := by
  have (U : X.Etaleᵒᵖ) : IsIso (((sheafToPresheaf _ _).map
      ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
        (Ideal.Quotient.mk (Ideal.span {ϖ}))).counit.app F)).app U) := by
    have hf := ModuleCat.mono_coextendQuotientShortComplex_f ϖ (F.obj.obj U)
    have he := ModuleCat.exact_coextendQuotientShortComplex ϖ (F.obj.obj U)
    rw [ShortComplex.moduleCat_exact_iff] at he
    change IsIso (ModuleCat.coextendQuotientShortComplex ϖ (F.obj.obj U)).f
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨(ModuleCat.mono_iff_injective _).1 hf, fun x ↦ he x (hF U x)⟩
  have : IsIso ((sheafToPresheaf _ _).map
      ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
        (Ideal.Quotient.mk (Ideal.span {ϖ}))).counit.app F)) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- A sheaf killed by `n` has its sections killed by `n` viewed in `Λ`. -/
lemma natCast_smul_eq_zero_of_nsmul_eq_zero {n : ℕ}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : n • 𝟙 F = 0)
    (U : X.Etaleᵒᵖ) (x : F.obj.obj U) : (n : Λ) • x = 0 := by
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
    sheafToPresheaf _ _ ⋙ (evaluation _ _).obj U
  have h : (E.map (n • 𝟙 F)).hom x = 0 := by rw [hF, E.map_zero]; rfl
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] at h
  rw [Nat.cast_smul_eq_nsmul]
  exact h

end Torsion

end AlgebraicGeometry.Etale
