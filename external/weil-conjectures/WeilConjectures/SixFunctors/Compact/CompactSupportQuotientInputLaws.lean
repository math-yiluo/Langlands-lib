/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData
public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientNative
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionDerivedIdentityUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData

/-! # Identity and composition of the normalized quotient reduction arrows

Source: blueprint coefficient quotient proof, Step 4; Stacks Tag 03EK.
(blueprint: lem-coef-compact-support-quotient-input-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

universe v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

private theorem input_unit
    {C : Type v₁} [Category.{w₁} C] {A : Type v₂} [Category.{w₂} A]
    {L : C ⥤ A} {R : A ⥤ C} (adj : L ⊣ R) (S : A ⥤ A)
    (e : S ⋙ R ≅ R) (i : S ≅ 𝟭 A) (K : C)
    (h : e.inv.app (L.obj K) ≫ R.map (i.hom.app (L.obj K)) = 𝟙 _) :
    (adj.homEquiv K _).symm (adj.unit.app K ≫ e.inv.app (L.obj K)) ≫
      i.hom.app (L.obj K) = 𝟙 _ := by
  apply (adj.homEquiv K _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc, h]
  rw [Adjunction.homEquiv_unit]
  exact congrArg (fun k ↦ adj.unit.app K ≫ k) (R.map_id (L.obj K)).symm

private theorem input_comp
    {C : Type v₁} [Category.{w₁} C] {A : Type v₂} [Category.{w₂} A]
    {B : Type v₃} [Category.{w₃} B] {T : Type v₄} [Category.{w₄} T]
    {Lr : C ⥤ A} {Rr : A ⥤ C} {Lm : C ⥤ B} {Rm : B ⥤ C}
    {Ln : C ⥤ T} {Rn : T ⥤ C}
    (ar : Lr ⊣ Rr) (am : Lm ⊣ Rm) (an : Ln ⊣ Rn)
    (S : B ⥤ A) (V : T ⥤ B) (Q : T ⥤ A)
    (erm : S ⋙ Rr ≅ Rm) (emn : V ⋙ Rm ≅ Rn) (ern : Q ⋙ Rr ≅ Rn)
    (c : V ⋙ S ≅ Q) (K : C)
    (h : emn.inv.app (Ln.obj K) ≫ erm.inv.app (V.obj (Ln.obj K)) ≫
      Rr.map (c.hom.app (Ln.obj K)) = ern.inv.app (Ln.obj K)) :
    (ar.homEquiv K _).symm (am.unit.app K ≫ erm.inv.app (Lm.obj K)) ≫
      S.map ((am.homEquiv K _).symm (an.unit.app K ≫ emn.inv.app (Ln.obj K))) ≫
      c.hom.app (Ln.obj K) =
    (ar.homEquiv K _).symm (an.unit.app K ≫ ern.inv.app (Ln.obj K)) := by
  let t := (am.homEquiv K _).symm (an.unit.app K ≫ emn.inv.app (Ln.obj K))
  apply (ar.homEquiv K _).injective
  rw [ar.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Functor.map_comp]
  change (am.unit.app K ≫ erm.inv.app (Lm.obj K)) ≫
    Rr.map (S.map t) ≫ Rr.map (c.hom.app (Ln.obj K)) = _
  have he := erm.inv.naturality t
  change Rm.map t ≫ erm.inv.app _ = erm.inv.app _ ≫ Rr.map (S.map t) at he
  have ht : am.unit.app K ≫ Rm.map t =
      an.unit.app K ≫ emn.inv.app (Ln.obj K) :=
    (am.homEquiv K _).apply_symm_apply _
  calc
    _ = (am.unit.app K ≫ Rm.map t) ≫ erm.inv.app (V.obj (Ln.obj K)) ≫
        Rr.map (c.hom.app (Ln.obj K)) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ am.unit.app K ≫ k ≫ Rr.map (c.hom.app (Ln.obj K))) he.symm
    _ = _ := by
      rw [ht]
      simpa only [Category.assoc] using congrArg (fun k ↦ an.unit.app K ≫ k) h

section Exact
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (S : A ⥤ A) (R : A ⥤ B) [S.Additive] [R.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private theorem exact_unit (i : S ≅ 𝟭 A) (e : S ⋙ R ≅ R)
    (he : e = Functor.isoWhiskerRight i R) (K : DerivedCategory A) :
    (Functor.exactDerivedRestrictionComposition S R R e).inv.app K ≫
      R.mapDerivedCategory.map ((Functor.exactDerivedRestrictionUnit S i).hom.app K) =
        𝟙 _ := by
  have h := exactRestrictionDerivedIdentityUnit R S i e
    (fun X ↦ congrArg (fun f ↦ f.hom.app X) he) K
  change (Functor.exactDerivedRestrictionComposition S R R e).hom.app K =
    R.mapDerivedCategory.map ((Functor.exactDerivedRestrictionUnit S i).hom.app K) at h
  rw [← h, Iso.inv_hom_id_app]

end Exact

private theorem basedEquality {I : Sort*} (a : I) (P : ∀ b, a = b → Prop)
    (ha : P a rfl) {b : I} (h : a = b) : P b h := by
  cases h
  exact ha

private theorem isoTrans_sections {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    {C : Type*} [Category C] {F G H : C ⥤ proEtaleRingModules W R}
    (a : F ≅ G) (b : G ≅ H) (M : C) (U : W.ProEtᵒᵖ)
    (x : (F.obj M).val.obj U) (y : (G.obj M).val.obj U) (z : (H.obj M).val.obj U)
    (ha : (a.hom.app M).val.app U x = y) (hb : (b.hom.app M).val.app U y = z) :
    ((a ≪≫ b).hom.app M).val.app U x = z := by
  simp only [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [ha, hb]

section Coefficients
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

omit [Finite A] [Finite B] [Finite C] in
private theorem coefficientCast_apply (W : Scheme.{u}) {φ ψ : A →+* B} (h : φ = ψ)
    (M : proEtaleRingModules W (proEtaleConstantRing W B))
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (((eqToIso (congrArg (proEtaleCoefficientRestrictScalars W) h)).hom.app M).val.app U) x =
      x := by
  exact basedEquality φ
    (fun ψ h ↦
      (((eqToIso (congrArg (proEtaleCoefficientRestrictScalars W) h)).hom.app M).val.app
        U) x = x) (by rfl) h

private theorem ordinaryId_apply (W : Scheme.{u}) (q : A →+* A)
    (hq : q = RingHom.id A) (M : proEtaleRingModules W (proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (((eqToIso (congrArg (proEtaleCoefficientRestrictScalars W) hq) ≪≫
      sfOpenCoefficientRestrictionId W A).hom.app M).val.app U) x = x := by
  exact isoTrans_sections (W := W) (R := proEtaleConstantRing W A)
    (F := proEtaleCoefficientRestrictScalars W q)
    (G := proEtaleCoefficientRestrictScalars W (RingHom.id A)) (H := 𝟭 _)
    (eqToIso (congrArg (proEtaleCoefficientRestrictScalars W) hq))
    (sfOpenCoefficientRestrictionId W A) M U x x x
    (coefficientCast_apply W hq M U x)
    (AlgebraicGeometry.Scheme.coefficientRestrictionId_apply W A M U x)

private theorem derivedId_eq (W : Scheme.{u}) (q : A →+* A)
    (hq : q = RingHom.id A) :
    compactSupportCoefficientResId W A q hq =
      Functor.exactDerivedRestrictionUnit (proEtaleCoefficientRestrictScalars W q)
        (eqToIso (congrArg (proEtaleCoefficientRestrictScalars W) hq) ≪≫
          sfOpenCoefficientRestrictionId W A) := by
  subst q
  simp only [compactSupportCoefficientResId, eqToIso_refl, Iso.refl_trans,
    Functor.exactDerivedRestrictionUnit, sfOpenDerivedCoefficientRestrictionId]

private def ordinaryComp (W : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (χ : A →+* C) (hχ : ψ.comp φ = χ) :
    proEtaleCoefficientRestrictScalars W ψ ⋙ proEtaleCoefficientRestrictScalars W φ ≅
      proEtaleCoefficientRestrictScalars W χ :=
  sfCoefficientRestrictionComp W φ ψ ≪≫
    eqToIso (congrArg (proEtaleCoefficientRestrictScalars W) hχ)

omit [Finite A] [Finite B] [Finite C] in
private theorem ordinaryComp_apply (W : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (χ : A →+* C) (hχ : ψ.comp φ = χ)
    (M : proEtaleRingModules W (proEtaleConstantRing W C)) (U : W.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((ordinaryComp W φ ψ χ hχ).hom.app M).val.app U x = x := by
  exact basedEquality (ψ.comp φ)
    (fun χ h ↦ ((ordinaryComp W φ ψ χ h).hom.app M).val.app U x = x)
    (by simpa only [ordinaryComp, eqToIso_refl, Iso.trans_refl] using
      AlgebraicGeometry.Scheme.coefficientComp_hom_apply W φ ψ M U x) hχ

omit [Finite A] [Finite B] [Finite C] in
private theorem derivedComp_eq (W : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (χ : A →+* C) (hχ : ψ.comp φ = χ) :
    compactSupportCoefficientResComp W φ ψ χ hχ =
      Functor.mapDerivedCategoryCompNatIso (ordinaryComp W φ ψ χ hχ) := by
  subst χ
  simp only [compactSupportCoefficientResComp, ordinaryComp, eqToIso_refl,
    Iso.trans_refl, sfDerivedCoefficientRestrictionComp,
    Functor.mapDerivedCategoryCompNatIso]

end Coefficients

private abbrev coefficientMap (W : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : proEtaleConstantRing W A ⟶ proEtaleConstantRing W B :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ.ulift)

private theorem restrictComp_apply {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (N : pbcModules W T) (U : W.ProEtᵒᵖ) (x : N.val.obj U) :
    ((pbcRestrictComp a b c h).hom.app N).val.app U x = x :=
  (pbcRestrictComp_exists a b c h).exists.choose_spec N U x

private theorem restrict_unit_sections {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (q : S ⟶ S) (h : a ≫ q = a)
    (i : pbcRestrict q ≅ 𝟭 (pbcModules W S))
    (hi : ∀ (N : pbcModules W S) (U : W.ProEtᵒᵖ) (x : N.val.obj U),
      (i.hom.app N).val.app U x = x) :
    pbcRestrictComp a q a h = Functor.isoWhiskerRight i (pbcRestrict a) := by
  apply Iso.ext
  ext N U x
  change ((pbcRestrictComp a q a h).hom.app N).val.app U x =
    (i.hom.app N).val.app U x
  rw [restrictComp_apply, hi]

private theorem restrict_comp_sections {W : Scheme.{u}}
    {R A B C : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ A) (ab : R ⟶ B) (abc : R ⟶ C)
    (φ : A ⟶ B) (ψ : B ⟶ C) (χ : A ⟶ C)
    (hab : a ≫ φ = ab) (hbc : ab ≫ ψ = abc) (hac : a ≫ χ = abc)
    (i : pbcRestrict ψ ⋙ pbcRestrict φ ≅ pbcRestrict χ)
    (hi : ∀ (N : pbcModules W C) (U : W.ProEtᵒᵖ) (x : N.val.obj U),
      (i.hom.app N).val.app U x = x) (N : pbcModules W C) :
    (pbcRestrict a).map (i.hom.app N) ≫ (pbcRestrictComp a χ abc hac).hom.app N =
      (pbcRestrictComp a φ ab hab).hom.app ((pbcRestrict ψ).obj N) ≫
        (pbcRestrictComp ab ψ abc hbc).hom.app N := by
  ext U x
  change ((pbcRestrictComp a χ abc hac).hom.app N).val.app U
      ((i.hom.app N).val.app U x) =
    ((pbcRestrictComp ab ψ abc hbc).hom.app N).val.app U
      (((pbcRestrictComp a φ ab hab).hom.app ((pbcRestrict ψ).obj N)).val.app U x)
  rw [restrictComp_apply, hi, restrictComp_apply, restrictComp_apply]

private theorem restriction_unit (W : Scheme.{u})
    {A : Type u} [CommRing A] [Finite A]
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ proEtaleConstantRing W A) (q : A →+* A) (hq : q = RingHom.id A)
    (h : a ≫ coefficientMap W q = a)
    (M : proEtaleDerivedCategory W A) :
    (pbcDerivedRestrictComp a (coefficientMap W q) a h).inv.app M ≫
      (pbcDerivedRestrict a).map ((compactSupportCoefficientResId W A q hq).hom.app M) =
        𝟙 _ := by
  let i := eqToIso (congrArg (proEtaleCoefficientRestrictScalars W) hq) ≪≫
    sfOpenCoefficientRestrictionId W A
  let e := pbcRestrictComp a (coefficientMap W q) a h
  have he : e = Functor.isoWhiskerRight i (pbcRestrict a) :=
    restrict_unit_sections a (coefficientMap W q) h i (ordinaryId_apply W q hq)
  rw [derivedId_eq]
  exact exact_unit (proEtaleCoefficientRestrictScalars W q) (pbcRestrict a) i e he M

private theorem restriction_comp (W : Scheme.{u})
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ proEtaleConstantRing W A) (ab : R ⟶ proEtaleConstantRing W B)
    (abc : R ⟶ proEtaleConstantRing W C)
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : ψ.comp φ = χ)
    (hab : a ≫ coefficientMap W φ = ab)
    (hbc : ab ≫ coefficientMap W ψ = abc)
    (hac : a ≫ coefficientMap W χ = abc) (M : proEtaleDerivedCategory W C) :
    (pbcDerivedRestrictComp ab (coefficientMap W ψ) abc hbc).inv.app M ≫
      (pbcDerivedRestrictComp a (coefficientMap W φ) ab hab).inv.app
        ((proEtaleCoefficientRestrictScalars W ψ).mapDerivedCategory.obj M) ≫
      (pbcDerivedRestrict a).map
        ((compactSupportCoefficientResComp W φ ψ χ hχ).hom.app M) =
      (pbcDerivedRestrictComp a (coefficientMap W χ) abc hac).inv.app M := by
  let e₁ := pbcRestrictComp a (coefficientMap W φ) ab hab
  let e₂ := pbcRestrictComp ab (coefficientMap W ψ) abc hbc
  let e₃ := pbcRestrictComp a (coefficientMap W χ) abc hac
  let e₄ := ordinaryComp W φ ψ χ hχ
  have ho := restrict_comp_sections a ab abc
    (coefficientMap W φ) (coefficientMap W ψ) (coefficientMap W χ) hab hbc hac e₄
    (ordinaryComp_apply W φ ψ χ hχ)
  have hd := Functor.mapDerivedCategoryCompNatIso_cocycle e₄ e₃ e₁ e₂ ho M
  change (pbcDerivedRestrict a).map ((Functor.mapDerivedCategoryCompNatIso e₄).hom.app M) ≫
      (pbcDerivedRestrictComp a (coefficientMap W χ) abc hac).hom.app M =
    (pbcDerivedRestrictComp a (coefficientMap W φ) ab hab).hom.app
        ((proEtaleCoefficientRestrictScalars W ψ).mapDerivedCategory.obj M) ≫
      (pbcDerivedRestrictComp ab (coefficientMap W ψ) abc hbc).hom.app M at hd
  apply (cancel_mono
    ((pbcDerivedRestrictComp a (coefficientMap W χ) abc hac).hom.app M)).mp
  rw [derivedComp_eq]
  simp only [Category.assoc]
  rw [hd]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionDerivedExtension completedIntegralCommRingProjectionUnrestricted
  compactSupportLevelQuotient

/-- The normalized quotient reductions satisfy identity and composition before applying
any geometric functor.

Source: blueprint `lem-coef-integral-compact-support.proof.md`, paragraph 2, and
Step 4 of `lem-coef-compact-support-quotient-cocycle`; Stacks Tag 03EK.
(blueprint: lem-coef-compact-support-quotient-input-laws).

Proof: the definition of rho is the unique transpose of the level-n unit under the
integral-to-level-m adjunction. On a common flat-term K-flat representative P, its
termwise formula is s tensor x to q(s) tensor x. For equal levels the quotient is the
identity. For r >= m >= n, the successive maps send s tensor x to
q_mn(q_rm(s)) tensor x = q_rn(s) tensor x. These identities hold on tensors,
descend through sheafification, and commute with differentials. Localization and the
normalized adjunct uniqueness identify these maps with the prescribed derived arrows.
The restriction identifications are exactly the sectionwise identities defining
compactSupportQuotientNativeResId and compactSupportQuotientNativeResComp. This applies to unbounded
P, the zero complex, and repeated indices, and uses no flatness of a quotient map. -/
theorem compactSupportQuotient_input_laws (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    (∀ n : ℕ, compactSupportQuotientNativeMap l E W n n le_rfl K ≫
      (compactSupportQuotientNativeResId l E W n).hom.app
        ((compactSupportQuotientNativeLevel l E W n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportQuotientNativeMap l E W r m hrm K ≫
          (compactSupportQuotientNativeRestriction l E W r m hrm).map
              (compactSupportQuotientNativeMap l E W m n hmn K) ≫
          (compactSupportQuotientNativeResComp l E W r m n hrm hmn).hom.app
            ((compactSupportQuotientNativeLevel l E W n).obj K) =
        compactSupportQuotientNativeMap l E W r n (hmn.trans hrm) K) := by
  constructor
  · intro n
    exact input_unit (L := compactSupportQuotientNativeLevel l E W n)
      (R := pbcDerivedRestrict
        (completedIntegralCommRingProjectionUnrestricted l E W n))
      (derivedScalarExtensionRestrictionAdjunction l E W n).choose
      (compactSupportQuotientNativeRestriction l E W n n le_rfl)
      (compactSupportRestrictionComp l E W n n le_rfl)
      (compactSupportQuotientNativeResId l E W n) K
      (restriction_unit W (completedIntegralCommRingProjectionUnrestricted l E W n)
        (compactSupportLevelQuotient l E n n le_rfl) (compactSupportQuotient_self l E n)
        (compactSupportProjection_comp l E W n n le_rfl) _)
  · intro r m n hrm hmn
    have hc := restriction_comp W (completedIntegralCommRingProjectionUnrestricted l E W r)
      (completedIntegralCommRingProjectionUnrestricted l E W m)
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (compactSupportLevelQuotient l E r m hrm) (compactSupportLevelQuotient l E m n hmn)
      (compactSupportLevelQuotient l E r n (hmn.trans hrm))
      (compactSupportQuotient_comp l E r m n hrm hmn)
      (compactSupportProjection_comp l E W r m hrm)
      (compactSupportProjection_comp l E W m n hmn)
      (compactSupportProjection_comp l E W r n (hmn.trans hrm))
      ((compactSupportQuotientNativeLevel l E W n).obj K)
    exact input_comp (Lr := compactSupportQuotientNativeLevel l E W r)
      (Lm := compactSupportQuotientNativeLevel l E W m)
      (Ln := compactSupportQuotientNativeLevel l E W n)
      (Rr := pbcDerivedRestrict
        (completedIntegralCommRingProjectionUnrestricted l E W r))
      (Rm := pbcDerivedRestrict
        (completedIntegralCommRingProjectionUnrestricted l E W m))
      (Rn := pbcDerivedRestrict
        (completedIntegralCommRingProjectionUnrestricted l E W n))
      (derivedScalarExtensionRestrictionAdjunction l E W r).choose
      (derivedScalarExtensionRestrictionAdjunction l E W m).choose
      (derivedScalarExtensionRestrictionAdjunction l E W n).choose
      (compactSupportQuotientNativeRestriction l E W r m hrm)
      (compactSupportQuotientNativeRestriction l E W m n hmn)
      (compactSupportQuotientNativeRestriction l E W r n (hmn.trans hrm))
      (compactSupportRestrictionComp l E W r m hrm)
      (compactSupportRestrictionComp l E W m n hmn)
      (compactSupportRestrictionComp l E W r n (hmn.trans hrm))
      (compactSupportQuotientNativeResComp l E W r m n hrm hmn) K
      hc

end WeilConjectures
