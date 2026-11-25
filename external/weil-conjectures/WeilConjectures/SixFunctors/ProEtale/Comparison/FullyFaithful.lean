/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-!
# Full faithfulness of the comparison pullback

Let `S` be a scheme and `A` a Grothendieck abelian category. We show that the unit
`F ⟶ ν_* ν^* F` of the comparison adjunction `ν^* ⊣ ν_*` between `A`-valued sheaves on the
small étale and the small pro-étale site of `S` is an isomorphism, so that
`ν^* : Sh(S_ét, A) ⥤ Sh(S_proét, A)` is fully faithful (Bhatt–Scholze, Corollary 5.1.6;
Stacks, Lemma 099T).

The proof follows the `Ab`-valued argument of the `proetale` package: on an object
`U = limᵢ Uᵢ` of the affine pro-étale site the presheaf pullback of an étale sheaf `F` is
the filtered colimit `colimᵢ F(Uᵢ)`
(`AlgebraicGeometry.Scheme.ProEt.preservesRelativeFilteredColimits_lan_toProEt`), so the
presheaf pullback is already a sheaf on the affine pro-étale site
(`AlgebraicGeometry.Scheme.ProEt.isSheaf_lan_toProEt`): this uses that filtered colimits are
exact in `A`. Since the affine pro-étale site is a dense subsite of the pro-étale site,
sheafification does not change the sections over affine étale `S`-schemes, which is what the
unit compares.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit_of_isGrothendieckAbelian`:
  the unit of `ν^* ⊣ ν_*` is an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- Viewing an affine étale `S`-scheme as an affine pro-étale one and then as an object of
`S_proét` agrees with taking `Spec` and then the inclusion `S_ét ⥤ S_proét`. -/
noncomputable
def AffineEtale.toAffineProEtCompToProEtIso :
    AffineEtale.toAffineProEt S ⋙ AffineProEt.toProEt S ≅
      AffineEtale.Spec S ⋙ Scheme.toProEt S :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

variable {S} in
/-- Since `ProEt.forget S` is fully faithful, mapping into `(ProEt.forget S).obj V` is
naturally isomorphic to mapping into `V`. -/
noncomputable def ProEt.forgetOpCompYonedaIso (V : S.ProEt) :
    (ProEt.forget S).op ⋙ yoneda.obj ((ProEt.forget S).obj V) ≅ yoneda.obj V :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso (ProEt.forgetFullyFaithful S).homEquiv.symm)
    (fun {U U'} f ↦ by
      ext g
      apply (ProEt.forget S).map_injective
      simp [Functor.FullyFaithful.homEquiv]
      rfl)


variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The presheaf pullback (i.e., the left Kan extension) of a presheaf on the small étale
site to the small pro-étale site sends cofiltered limits of affine étale `S`-schemes to
colimits, when restricted to the small affine pro-étale site.

The key input is `AlgebraicGeometry.Scheme.preservesColimit_yoneda`: maps out of a
cofiltered limit of quasi-compact, quasi-separated schemes into a scheme locally of finite
presentation over the base are a filtered colimit of hom sets. -/
instance ProEt.preservesRelativeFilteredColimits_lan_toProEt (F : S.Etaleᵒᵖ ⥤ A) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  constructor
  intro I _ _ K c hc
  -- The limit cone in the pro-étale site.
  have hc₁ : IsLimit ((AffineProEt.toProEt S).mapCone c) := isLimitOfPreserves _ hc
  -- The limit cone in `Over S`, obtained by reflecting the `Scheme`-level limit cone
  -- along `Over.forget S`.
  have hcOver : IsLimit ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)) :=
    isLimitOfReflects (CategoryTheory.Over.forget S)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc).ofIsoLimit
        (Functor.mapConeMapCone c).symm).ofIsoLimit (Functor.mapConeMapCone _).symm)
  -- The comparison of the two relevant diagrams in the pro-étale site.
  have e : (K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S ≅
      (K ⋙ AffineEtale.Spec S) ⋙ Scheme.toProEt S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft K (AffineEtale.toAffineProEtCompToProEtIso S) ≪≫
      (Functor.associator _ _ _).symm
  -- Mapping into an étale `S`-scheme commutes with the cofiltered limit, by
  -- `Scheme.preservesColimit_yoneda`.
  have hpres : ∀ (X : S.Etaleᵒᵖ),
      PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op)
        (coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))) := by
    intro X
    have h₁ : ∀ {i j : I} (f : i ⟶ j), IsAffineHom
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).map f).left :=
      fun f ↦ inferInstanceAs
        (IsAffineHom ((AffineEtale.toAffineProEt S).map (K.map f)).left)
    have h₂ : ∀ (i : I), CompactSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs (CompactSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₃ : ∀ (i : I), QuasiSeparatedSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs
        (QuasiSeparatedSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₄ : LocallyOfFinitePresentation
        ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation X.unop.hom)
    have := Scheme.preservesColimit_yoneda
      (((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙ ProEt.forget S)
      ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop))
    have hyon : IsColimit
        ((yoneda.obj ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop))).mapCocone
          ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)).op) :=
      isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj ((Scheme.toProEt S).obj X.unop)).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso ((Scheme.toProEt S).obj X.unop))
        (by exact hyon)
    have hco : IsColimit ((coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (Coyoneda.objOpOp _).symm hy
    let : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
        (coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))) :=
      preservesColimit_of_preserves_colimit_cocone hc₁.op hco
    exact preservesColimit_of_iso_diagram _ (NatIso.op e).symm
  let : PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op)
      ((Scheme.toProEt S).op.leftKanExtension F) := inferInstance
  have e' : (K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op ≅
      ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op := NatIso.op e
  let : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
      ((Scheme.toProEt S).op.leftKanExtension F) :=
    preservesColimit_of_iso_diagram _ e'
  exact ⟨isColimitOfPreserves ((Scheme.toProEt S).op.leftKanExtension F) hc₁.op⟩

/-- If `F` is a sheaf on the small étale site, the presheaf pullback of `F`
to the small pro-étale site (i.e., the left Kan extension) is a
sheaf when restricted to the small affine pro-étale site. -/
lemma ProEt.isSheaf_lan_toProEt (F : S.Etaleᵒᵖ ⥤ A)
    (hF : Presheaf.IsSheaf (smallEtaleTopology S) F) :
    Presheaf.IsSheaf (AffineProEt.topology S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  have : HasFilteredColimitsOfSize.{u, u} A :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} A := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} A
  apply Presheaf.isSheaf_of_generates_of_isRelativelyPresentable
      (AffineEtale.toAffineProEt S) (AffineProEt.minimalPrecoverage S)
      (AffineEtale.topology S)
  · let iso : (AffineEtale.toAffineProEt S).op ⋙
        (AffineProEt.toProEt S).op ⋙ S.toProEt.op.lan.obj F ≅
        (AffineEtale.Spec S).op ⋙ F :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _).symm _ ≪≫
        Functor.isoWhiskerRight (NatIso.op (AffineEtale.toAffineProEtCompToProEtIso S).symm) _ ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (asIso <| ((Scheme.toProEt S).op.lanUnit.app F)).symm
    rw [Presheaf.isSheaf_of_iso_iff iso]
    exact Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ hF
  · exact AffineProEt.generates_minimalPrecoverage S
  · exact AffineProEt.minimalPrecoverage_le_relativelyPresentable S
  · exact AffineProEt.minimalPrecoverage_le_finite S


end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

lemma comparisonAdjunction_unit_app_hom (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology A) :
    ((comparisonAdjunction A X).unit.app F).hom =
      (toProEt X).op.lanUnit.app F.obj ≫
        (toProEt X).op.whiskerLeft (toSheafify _ ((toProEt X).op.lan.obj F.obj)) := by
  change (sheafToPresheaf _ A).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).unit.app F) = _
  rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp

/-- Blueprint `theorem-bounded-below-cohomology-comparison`: The pro-étale comparison

*Full faithfulness, in the form the chapter uses.* The unit `id ⟶ ν_* ν^*` of the comparison
adjunction is an isomorphism; this is the assertion `id ≅ Rν_{T*} ν_T^*` of the blueprint, and
it is strictly stronger than the existence of some isomorphism between the two functors.

Detection of isomorphisms is by covering families and on the affine ind-étale basis, not by
geometric points: geometric-point stalks are *not* conservative on all pro-étale sheaves, and
no argument of the purity chapter uses them off the étale-origin objects. -/
theorem isIso_comparisonAdjunction_unit (X : Scheme.{u}) :
    IsIso (comparisonAdjunction A X).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let G := (AffineEtale.Spec X).sheafPushforwardContinuous A (AffineEtale.topology X)
    X.smallEtaleTopology
  suffices IsIso ((G ⋙ sheafToPresheaf _ A).map ((comparisonAdjunction A X).unit.app F)) from
    isIso_of_reflects_iso _ (G ⋙ sheafToPresheaf _ A)
  change IsIso ((AffineEtale.Spec X).op.whiskerLeft ((comparisonAdjunction A X).unit.app F).hom)
  rw [comparisonAdjunction_unit_app_hom, Functor.whiskerLeft_comp]
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  have h2 : IsIso ((AffineProEt.toProEt X).op.whiskerLeft
      (toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj F.obj))) :=
    Functor.IsDenseSubsite.isIso_whiskerLeft_toSheafify (AffineProEt.topology X) _ _ A _
      (ProEt.isSheaf_lan_toProEt X A F.obj F.property)
  have h3 : IsIso ((AffineEtale.Spec X).op.whiskerLeft ((toProEt X).op.whiskerLeft
      (toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj F.obj)))) := by
    rw [NatTrans.isIso_iff_isIso_app] at h2 ⊢
    intro U
    exact h2 (Opposite.op ((AffineEtale.toAffineProEt X).obj U.unop))
  infer_instance

/-- Blueprint `theorem-bounded-below-cohomology-comparison`: The pro-étale comparison

*Fullness.* The comparison pullback is full. -/
instance full_comparisonUpperStar (X : Scheme.{u}) : (comparisonUpperStar A X).Full :=
  have := isIso_comparisonAdjunction_unit A X
  (comparisonAdjunction A X).full_L_of_isSplitEpi_unit_app

/-- Blueprint `theorem-bounded-below-cohomology-comparison`: The pro-étale comparison

*Faithfulness.* The comparison pullback is faithful. -/
instance faithful_comparisonUpperStar (X : Scheme.{u}) : (comparisonUpperStar A X).Faithful :=
  have := isIso_comparisonAdjunction_unit A X
  (comparisonAdjunction A X).faithful_L_of_mono_unit_app

end AlgebraicGeometry.ProEtale
