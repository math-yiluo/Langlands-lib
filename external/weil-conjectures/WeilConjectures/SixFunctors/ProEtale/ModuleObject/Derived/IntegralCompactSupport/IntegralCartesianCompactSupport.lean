/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompCompositionBaseChange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBoundaryExchange

/-! # Coherence portions for integral compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  upperStarFromPoint derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  upperStarLowerStarAdjunction upperStar lowerStar openImmersionLowerShriek
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.monoidalCategory Mod.monoidalCategoryStruct
  Sheaf.monoidalCategory DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  condensedAmbientExchange condensedAmbientPullbackComparison
  Compactification.inf Compactification.infFst Compactification.infSnd

private theorem cartesianOpenExchange_isIso
    {X Z X' Z' : Scheme.{u}} {j : X ⟶ Z} {w : Z' ⟶ Z}
    {j' : X' ⟶ Z'} {u' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback u' j' j w) :
    IsIso (openExchange Λ sq.toCommSq) := by
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    refinementOpenUnit_isIso Λ j
  have hu : IsIso (openAdjunction Λ j).unit := by
    simp only [openAdjunction, Adjunction.ofNatIsoRight_unit]
    infer_instance
  let := hu
  unfold openExchange
  apply openExchange_isIso (extend Λ j) (pull Λ j) (pull Λ w) (pull Λ u')
    (extend Λ j') (pull Λ j') (openAdjunction Λ j) (openAdjunction Λ j')
    (pullSquare Λ sq.toCommSq.flip)
  intro K
  let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ w).app
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ j) (upperStar Λ w)).app K
  have hc := cartesianDerivedCounit Λ sq K
  have ht : IsIso
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').counit.app
        ((pull Λ w).obj ((extend Λ j).obj K))) :=
    (NatTrans.isIso_app_iff_of_iso _ e).mpr hc
  simp only [openAdjunction, Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app]
  infer_instance

private theorem baseChange_isIso_of_proper
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (ho : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq))
    (K : Ambient Λ X)
    (hp : IsIso ((pushExchange Λ
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app ((extend Λ c.i).obj K))) :
    IsIso ((baseChange Λ c sq ho).app K) := by
  exact baseChangeIsIsoOfProper Λ c sq ho K hp

private theorem transport_eq_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (θ : G ⋙ L₂ ≅ L₁ ⋙ H) :
    (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ b.unit ≫
        (Functor.squareTransport R₁ R₂ θ).hom ≫
        Functor.whiskerRight a.counit _ ≫ (Functor.leftUnitor _).hom =
      (mateEquiv a b (TwoSquare.mk _ _ _ _ θ.hom)) := by
  ext K
  simp only [mateEquiv, Equiv.coe_fn_mk,
    NatTrans.comp_app, Functor.squareTransport_hom_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.comp_obj, Functor.comp_map, Category.id_comp]

private theorem pushExchange_eq_ambient
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {v : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : ChosenCartesianSquare u' f' f v) :
    pushExchange Λ sq.toCommSq = condensedAmbientExchange Λ sq := by
  have hθ : pullSquare Λ sq.toCommSq = condensedAmbientPullbackComparison Λ sq := by
    unfold pullSquare condensedAmbientPullbackComparison
    rfl
  simpa only [pushExchange, condensedAmbientExchange, ← hθ, pull, push,
    moduleDerivedPullback, moduleDerivedPushforward] using
    transport_eq_mate (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f') (pullSquare Λ sq.toCommSq)

/-- Open-extension preservation in the cached module-object interface. -/
private theorem openExtension_cached
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U Z : Scheme.{u}} [U.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (j : U ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (K : Ambient Λ U) (hK : localizingClosureProEtale Λ U K) :
    localizingClosureProEtale Λ Z ((extend Λ j).obj K) := by
  obtain ⟨_, _, hmap, _, _⟩ :=
    (openImmersionLowerShriek_localizing ℓ k (ringChar k)
      (Nat.Prime.pos Fact.out) (Fact.out : ringChar k ≠ ℓ) Λ hΛ j).2.2
  exact hmap ⟨K, hK⟩

/-- Translate the admissible proper-exchange theorem to the cached module categories
before specializing the coefficient ring. Retain the supplied commutativity witness
in the conclusion, identifying witnesses while all four schemes are abstract. -/
private theorem properExchange_cached
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [A.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (A ↘ Spec (.of k))] [QuasiCompact (A ↘ Spec (.of k))]
    [IsSeparated (A ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} [q'.IsOver (Spec (.of k))] [IsProper q']
    (p : CommSq a q' q v) (sq : ChosenCartesianSquare a q' q v)
    (K : Ambient Λ Z) (hK : localizingClosureProEtale Λ Z K) :
    IsIso ((pushExchange Λ p).app K) := by
  have hqc (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [QuasiCompact (T ↘ Spec (.of k))] : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have hqs (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] : QuasiSeparatedSpace T :=
    quasiSeparatedSpace_of_quasiSeparated (T ↘ Spec (.of k))
  have := hqc A
  have := hqc Z
  have := hqc Y
  have := hqc Y'
  have := hqs A
  have := hqs Z
  have := hqs Y
  have := hqs Y'
  have hp : p = sq.toCommSq := Subsingleton.elim _ _
  rw [hp, pushExchange_eq_ambient Λ sq]
  exact properExchange_admissible ℓ Λ hΛ k q v sq
    (properLocalizingHypotheses_admissible ℓ Λ hΛ k q')
    ((pullback_of_constructible Λ v (pullback_constructible Λ v)).some)
    ((pullback_of_constructible Λ a (pullback_constructible Λ a)).some) K hK

variable (k : Type u) [Field k]

private theorem spaces_compact (X : Spaces k) : CompactSpace X.obj.left :=
  let := X.property.2.2
  QuasiCompact.compactSpace_of_compactSpace X.obj.hom

private theorem spaces_quasiSeparated (X : Spaces k) : QuasiSeparatedSpace X.obj.left :=
  let := X.property.1
  quasiSeparatedSpace_of_quasiSeparated X.obj.hom

private theorem localizing_eq_ctf (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Spaces k) :
    localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left =
      localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left := by
  let := spaces_compact k X
  let := spaces_quasiSeparated k X
  exact (localizingClosure_ctf_equals_bc ℓ X.obj.left
    (Profinite.padicIntegersRingObj ℓ E.val)
    (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.2.1.symm

/-- Proper exchange on an open extension for an arbitrary admissible coefficient.
Keeping the coefficient abstract shares all category-instance conversions. -/
private theorem properExchange_on_extension_admissible
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y X' Y' : Spaces k} (f : X ⟶ Y) (v : Y' ⟶ Y)
    (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactifications k f) (K : Ambient Λ X.obj.left)
    (hK : localizingClosureProEtale Λ X.obj.left K) :
    IsIso ((pushExchange Λ (c.obj.isPullback_g_ofIsPullback sq).flip.toCommSq).app
      ((extend Λ c.obj.i).obj K)) := by
  let : X.obj.left.Over (Spec (.of k)) := ⟨X.obj.hom⟩
  let : Y.obj.left.Over (Spec (.of k)) := ⟨Y.obj.hom⟩
  let : Y'.obj.left.Over (Spec (.of k)) := ⟨Y'.obj.hom⟩
  have : LocallyOfFiniteType X.obj.hom := X.property.2.1
  have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of k)) := X.property.2.1
  have : QuasiCompact X.obj.hom := X.property.2.2
  have : QuasiCompact (X.obj.left ↘ Spec (.of k)) := X.property.2.2
  have : IsSeparated X.obj.hom := X.property.1
  have : IsSeparated (X.obj.left ↘ Spec (.of k)) := X.property.1
  have : LocallyOfFiniteType Y.obj.hom := Y.property.2.1
  have : LocallyOfFiniteType (Y.obj.left ↘ Spec (.of k)) := Y.property.2.1
  have : QuasiCompact Y.obj.hom := Y.property.2.2
  have : QuasiCompact (Y.obj.left ↘ Spec (.of k)) := Y.property.2.2
  have : IsSeparated Y.obj.hom := Y.property.1
  have : IsSeparated (Y.obj.left ↘ Spec (.of k)) := Y.property.1
  have : LocallyOfFiniteType Y'.obj.hom := Y'.property.2.1
  have : LocallyOfFiniteType (Y'.obj.left ↘ Spec (.of k)) := Y'.property.2.1
  have : QuasiCompact Y'.obj.hom := Y'.property.2.2
  have : QuasiCompact (Y'.obj.left ↘ Spec (.of k)) := Y'.property.2.2
  have : IsSeparated Y'.obj.hom := Y'.property.1
  have : IsSeparated (Y'.obj.left ↘ Spec (.of k)) := Y'.property.1
  have : f.hom.left.IsOver (Spec (.of k)) := ⟨f.hom.w⟩
  have : v.hom.left.IsOver (Spec (.of k)) := ⟨v.hom.w⟩
  let : c.obj.Z.Over (Spec (.of k)) := ⟨c.obj.g ≫ Y.obj.hom⟩
  have : c.obj.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsSeparated (c.obj.Z ↘ Spec (.of k)) := by
    change IsSeparated (c.obj.g ≫ Y.obj.hom)
    infer_instance
  have : LocallyOfFiniteType (c.obj.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (c.obj.g ≫ Y.obj.hom)
    infer_instance
  have : QuasiCompact (c.obj.Z ↘ Spec (.of k)) := by
    change QuasiCompact (c.obj.g ≫ Y.obj.hom)
    infer_instance
  have : c.obj.i.IsOver (Spec (.of k)) := ⟨by
    change c.obj.i ≫ c.obj.g ≫ Y.obj.hom = X.obj.hom
    rw [← Category.assoc, ← c.obj.comm]
    exact f.hom.w⟩
  have hj := openExtension_cached Λ ℓ hΛ k c.obj.i K hK
  let : (c.obj.ofIsPullback sq).Z.Over (Spec (.of k)) :=
    ⟨(c.obj.ofIsPullback sq).g ≫ Y'.obj.hom⟩
  have : (c.obj.ofIsPullback sq).g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsSeparated ((c.obj.ofIsPullback sq).Z ↘ Spec (.of k)) := by
    change IsSeparated ((c.obj.ofIsPullback sq).g ≫ Y'.obj.hom)
    infer_instance
  have : LocallyOfFiniteType ((c.obj.ofIsPullback sq).Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType ((c.obj.ofIsPullback sq).g ≫ Y'.obj.hom)
    infer_instance
  have : QuasiCompact ((c.obj.ofIsPullback sq).Z ↘ Spec (.of k)) := by
    change QuasiCompact ((c.obj.ofIsPullback sq).g ≫ Y'.obj.hom)
    infer_instance
  let psq : ChosenCartesianSquare
      (X' := (c.obj.ofIsPullback sq).Z) (pullback.fst c.obj.g v.hom.left)
      (c.obj.ofIsPullback sq).g c.obj.g v.hom.left :=
    { toCommSq := (c.obj.isPullback_g_ofIsPullback sq).flip.toCommSq
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  exact properExchange_cached Λ ℓ hΛ k c.obj.g v.hom.left
    (c.obj.isPullback_g_ofIsPullback sq).flip.toCommSq psq
    ((extend Λ c.obj.i).obj K) hj

private theorem properExchange_on_extension (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y X' Y' : Spaces k} (f : X ⟶ Y) (v : Y' ⟶ Y)
    (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactifications k f)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left).FullSubcategory) :
    IsIso ((pushExchange (Profinite.padicIntegersRingObj ℓ E.val)
      (c.obj.isPullback_g_ofIsPullback sq).flip.toCommSq).app
        ((extend (Profinite.padicIntegersRingObj ℓ E.val) c.obj.i).obj K.obj)) := by
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ
      (Profinite.padicIntegersRingObj ℓ E.val) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  have hK : localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val)
      X.obj.left K.obj := by
    rw [← localizing_eq_ctf k ℓ E X]
    exact K.property
  exact properExchange_on_extension_admissible (Profinite.padicIntegersRingObj ℓ E.val)
    ℓ hΛ k f v f' u' sq c K.obj hK

private theorem base_boundary {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) {c d : Compactification f}
    (r : c.Refinement d) (hr : r.hom ⁻¹ᵁ d.i.opensRange = c.i.opensRange) :
    (r.ofIsPullback sq).hom ⁻¹ᵁ (d.ofIsPullback sq).i.opensRange =
      (c.ofIsPullback sq).i.opensRange := by
  have ranges (a : Compactification f) :
      (a.ofIsPullback sq).i.opensRange = pullback.fst a.g v ⁻¹ᵁ a.i.opensRange := by
    apply SetLike.coe_injective
    exact range_snd_of_isPullback (a.isPullback_i_ofIsPullback sq)
  let r' : pullback c.g v ⟶ pullback d.g v := (r.ofIsPullback sq).hom
  let jc : X' ⟶ pullback c.g v := (c.ofIsPullback sq).i
  let jd : X' ⟶ pullback d.g v := (d.ofIsPullback sq).i
  have : IsOpenImmersion jc := (c.ofIsPullback sq).isOpenImmersion
  have : IsOpenImmersion jd := (d.ofIsPullback sq).isOpenImmersion
  change r' ⁻¹ᵁ jd.opensRange = jc.opensRange
  have hc : jc.opensRange = pullback.fst c.g v ⁻¹ᵁ c.i.opensRange := ranges c
  have hd : jd.opensRange = pullback.fst d.g v ⁻¹ᵁ d.i.opensRange := ranges d
  have hr' : r' ≫ pullback.fst d.g v = pullback.fst c.g v ≫ r.hom :=
    Compactification.Refinement.ofIsPullback_hom_fst sq r
  calc
    r' ⁻¹ᵁ jd.opensRange = r' ⁻¹ᵁ (pullback.fst d.g v ⁻¹ᵁ d.i.opensRange) :=
      congrArg (fun U ↦ r' ⁻¹ᵁ U) hd
    _ = (r' ≫ pullback.fst d.g v) ⁻¹ᵁ d.i.opensRange :=
      (Scheme.Hom.comp_preimage _ _ _).symm
    _ = (pullback.fst c.g v ≫ r.hom) ⁻¹ᵁ d.i.opensRange :=
      congrArg (fun h ↦ h ⁻¹ᵁ d.i.opensRange) hr'
    _ = pullback.fst c.g v ⁻¹ᵁ (r.hom ⁻¹ᵁ d.i.opensRange) :=
      Scheme.Hom.comp_preimage _ _ _
    _ = pullback.fst c.g v ⁻¹ᵁ c.i.opensRange :=
      congrArg (fun U ↦ pullback.fst c.g v ⁻¹ᵁ U) hr
    _ = jc.opensRange := hc.symm

private def commonData {X Y : Spaces k} (f : X ⟶ Y)
    (c d : Compactifications k f) :
    Σ q : Compactifications k f,
      {r : q.obj.Refinement c.obj //
        r.hom ⁻¹ᵁ c.obj.i.opensRange = q.obj.i.opensRange} ×
      {r : q.obj.Refinement d.obj //
        r.hom ⁻¹ᵁ d.obj.i.opensRange = q.obj.i.opensRange} := by
  let := spaces_compact k Y
  let := spaces_quasiSeparated k Y
  let : X.obj.left.Over (Spec (.of k)) := ⟨X.obj.hom⟩
  let : Y.obj.left.Over (Spec (.of k)) := ⟨Y.obj.hom⟩
  have : IsSeparated X.obj.hom := X.property.1
  have : IsSeparated (X.obj.left ↘ Spec (.of k)) := X.property.1
  have : LocallyOfFiniteType X.obj.hom := X.property.2.1
  have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of k)) := X.property.2.1
  have : QuasiCompact X.obj.hom := X.property.2.2
  have : QuasiCompact (X.obj.left ↘ Spec (.of k)) := X.property.2.2
  have : IsSeparated Y.obj.hom := Y.property.1
  have : IsSeparated (Y.obj.left ↘ Spec (.of k)) := Y.property.1
  have : f.hom.left.IsOver (Spec (.of k)) := ⟨f.hom.w⟩
  have : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    exact X.property.1
  have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    exact X.property.2.1
  have : QuasiCompact (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    exact X.property.2.2
  have := IsSeparated.of_comp f.hom.left Y.obj.hom
  have := locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
  have := QuasiCompact.of_comp f.hom.left Y.obj.hom
  have hcommon :=
    Compactification.exists_common_dense_refinement.{u, 0} f.hom.left c.obj d.obj
  exact ⟨⟨Compactification.inf c.obj d.obj, hcommon.2.2.1⟩,
    ⟨Compactification.infFst c.obj d.obj, hcommon.2.2.2.2.2.2.2.2.2.2.2.1⟩,
    ⟨Compactification.infSnd c.obj d.obj, hcommon.2.2.2.2.2.2.2.2.2.2.2.2.1⟩⟩

attribute [local irreducible] commonData

private theorem comparison_from_common
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₀ A₁ A₂ : C} {B₀ B₁ B₂ : D}
    (ρ₁ : A₀ ≅ A₁) (ρ₂ : A₀ ⟶ A₂) (φ : A₁ ⟶ A₂)
    (σ₁ : B₀ ⟶ B₁) (σ₂ : B₀ ⟶ B₂) (ψ : B₁ ⟶ B₂)
    (β₀ : F.obj A₀ ⟶ B₀) (β₁ : F.obj A₁ ⟶ B₁) (β₂ : F.obj A₂ ⟶ B₂)
    (hφ : ρ₁.hom ≫ φ = ρ₂) (hψ : σ₁ ≫ ψ = σ₂)
    (h₁ : F.map ρ₁.hom ≫ β₁ = β₀ ≫ σ₁)
    (h₂ : F.map ρ₂ ≫ β₂ = β₀ ≫ σ₂) :
    F.map φ ≫ β₂ = β₁ ≫ ψ := by
  apply (cancel_epi (F.map ρ₁.hom)).1
  rw [← Category.assoc, ← F.map_comp, hφ, h₂, ← hψ, ← Category.assoc,
    ← h₁, Category.assoc]

/-- The normalization hypotheses give the exchange equation for one boundary refinement.
The coefficient ring is kept abstract while comparing the two chosen normalizations. -/
private theorem normalizedComparison_baseChange
    (φ : Comparisons Λ k)
    (hn : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing Λ X.obj.left).FullSubcategory),
      ∃ e : (extend Λ d.obj.i).obj K.obj ≅
          (push Λ r.hom).obj ((extend
            Λ c.obj.i).obj K.obj),
        (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction Λ r K.obj =
              (openAdjunction Λ c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso Λ r K.obj e)
    (localizing_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient Λ Y.obj.left),
    localizing Λ Y.obj.left K →
      localizing Λ X.obj.left ((pull
        Λ v.hom.left).obj K))
    {X Y X' Y' : Spaces k}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c d : Compactifications k f) (r : c.obj.Refinement d.obj)
    (hr : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (ho : IsIso (openExchange Λ (c.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange Λ (d.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (K : (localizing Λ X.obj.left).FullSubcategory) :
    (pull Λ v.hom.left).map ((φ f c d).hom.app K) ≫
        (baseChange Λ d.obj sq hd).app K.obj =
      (baseChange Λ c.obj sq ho).app K.obj ≫
        (φ f' (baseCompactification k c sq) (baseCompactification k d sq)).hom.app
          ⟨(pull Λ u'.hom.left).obj K.obj, localizing_pull u' K.obj K.property⟩ := by
  let K' : (localizing Λ X'.obj.left).FullSubcategory :=
    ⟨(pull Λ u'.hom.left).obj K.obj, localizing_pull u' K.obj K.property⟩
  obtain ⟨e, he, hφ⟩ := hn f c d r hr K
  have hn' := hn f' (baseCompactification k c sq) (baseCompactification k d sq)
  dsimp only [baseCompactification] at hn'
  have hrb := base_boundary (c := c.obj) (d := d.obj) sq r hr
  have hnr := hn' (r.ofIsPullback sq)
  have hnb := hnr hrb
  obtain ⟨e', he', hφ'⟩ := hnb K'
  have h₁ := congrArg Iso.hom hφ
  have h₂ := congrArg Iso.hom hφ'
  simp only [Iso.app_hom] at h₁ h₂
  dsimp only [baseCompactification] at h₂ ⊢
  rw [h₁, h₂]
  exact normalizedBoundaryExchange Λ sq c.obj d.obj r hr ho hd K.obj e he e' he'

/-- Comparison compatibility is formal in the coefficient: it uses one common
boundary refinement, normalization, and the comparison cocycle. -/
private theorem cartesianComparisons_compatible
    (φ : Comparisons Λ k)
    (hc : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d e : Compactifications k f),
    φ f c d ≪≫ φ f d e = φ f c e)
    (hn : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing Λ X.obj.left).FullSubcategory),
      ∃ e : (extend Λ d.obj.i).obj K.obj ≅
          (push Λ r.hom).obj ((extend
            Λ c.obj.i).obj K.obj),
        (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction Λ r K.obj =
              (openAdjunction Λ c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso Λ r K.obj e)
    (localizing_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient Λ Y.obj.left),
    localizing Λ Y.obj.left K →
      localizing Λ X.obj.left ((pull
        Λ v.hom.left).obj K)) :
    ∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c d : Compactifications k f)
    (hc : IsIso (openExchange Λ
      (c.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange Λ
      (d.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (K : (localizing Λ X.obj.left).FullSubcategory),
      (pull Λ v.hom.left).map ((φ f c d).hom.app K) ≫
          (baseChange Λ d.obj sq hd).app K.obj =
        (baseChange Λ c.obj sq hc).app K.obj ≫
          (φ f' (baseCompactification k c sq) (baseCompactification k d sq)).hom.app
            ⟨(pull Λ u'.hom.left).obj K.obj,
              localizing_pull u' K.obj K.property⟩ := by
  intro X Y X' Y' f v f' u' sq c d ho hd K
  let K' : (localizing Λ X'.obj.left).FullSubcategory :=
    ⟨(pull Λ u'.hom.left).obj K.obj, localizing_pull u'
      K.obj K.property⟩
  let data := commonData k f c d
  let q := data.1
  let r₁ := data.2.1.1
  let r₂ := data.2.2.1
  let q' := baseCompactification k q sq
  have hq := cartesianOpenExchange_isIso Λ
    (q.obj.isPullback_i_ofIsPullback sq)
  have normalized (a : Compactifications k f) (r : q.obj.Refinement a.obj)
      (hr : r.hom ⁻¹ᵁ a.obj.i.opensRange = q.obj.i.opensRange)
      (ha : IsIso (openExchange Λ
        (a.obj.isPullback_i_ofIsPullback sq).toCommSq)) :
      (pull Λ v.hom.left).map ((φ f q a).hom.app K) ≫
          (baseChange Λ a.obj sq ha).app K.obj =
        (baseChange Λ q.obj sq hq).app K.obj ≫
          (φ f' q' (baseCompactification k a sq)).hom.app K' := by
    exact normalizedComparison_baseChange Λ k φ hn
      localizing_pull sq q a r hr hq ha K
  have h₁ := normalized c r₁ data.2.1.2 ho
  have h₂ := normalized d r₂ data.2.2.2 hd
  have hφ := congrArg (fun e ↦ e.hom.app K) (hc f q c d)
  have hφ' := congrArg (fun e ↦ e.hom.app K')
    (hc f' q' (baseCompactification k c sq) (baseCompactification k d sq))
  exact comparison_from_common (pull Λ v.hom.left) ((φ f
    q c).app K)
    ((φ f q d).hom.app K) ((φ f c d).hom.app K)
    ((φ f' q' (baseCompactification k c sq)).hom.app K')
    ((φ f' q' (baseCompactification k d sq)).hom.app K')
    ((φ f' (baseCompactification k c sq) (baseCompactification k d sq)).hom.app K')
    ((baseChange Λ q.obj sq hq).app K.obj)
    ((baseChange Λ c.obj sq ho).app K.obj)
    ((baseChange Λ d.obj sq hd).app K.obj) hφ hφ' h₁ h₂

-- Keep the published preservation and identity hypotheses with their original names.
set_option linter.unusedVariables false in
/-- Cartesian base change with the total-derived open adjunction normalization.

Source: blueprint proposition-composition-base-change-rf-shriek--4, proof steps 1--8,
and proposition-construction-independence-rf-shriek step 7.
(blueprint: lem-sfb-total-derived-cartesian-compact-support).

Proof: the proper leg of the base-changed compactification is already the literal
proper pullback. Transport the invertible derived open unit and the Cartesian derived
counit along leftDerivedUpperStarIsoMapDerivedCategory to prove openExchange invertible.
The squareTransport formula identifies pushExchange with the ambient proper mate.
For O_E, Loc(Dbc) equals Loc(Dctf); open extension preserves that category, and admissible
proper base change makes its proper-exchange components invertible. The component API
then gives invertibility of baseChange.
For compatibility choose one common boundary-preserving refinement of c and d.
Its pullback remains boundary-preserving by inverse images of the open ranges; density
after pullback is not needed. Use hn before and after pullback and the single-refinement
normalizedBoundaryExchange equation. The two comparison cocycles and cancellation of
an invertible common-refinement comparison give the required equation for φ. No choices
of isomorphisms are made beyond those supplied by hn. Proof irrelevance handles hc and hd.
This argument includes zero objects and empty opens. -/
theorem cartesianCompactSupport
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (h : Preservation (Profinite.padicIntegersRingObj ℓ E.val) k) (φ : Comparisons
      (Profinite.padicIntegersRingObj ℓ E.val) k)
    (hi : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c : Compactifications k f),
    φ f c c = Iso.refl _)
    (hc : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d e : Compactifications k f),
    φ f c d ≪≫ φ f d e = φ f c e)
    (hn : ∀ {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (_boundary : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left).FullSubcategory),
      ∃ e : (extend (Profinite.padicIntegersRingObj ℓ E.val) d.obj.i).obj K.obj ≅
          (push (Profinite.padicIntegersRingObj ℓ E.val) r.hom).obj ((extend
            (Profinite.padicIntegersRingObj ℓ E.val) c.obj.i).obj K.obj),
        (openAdjunction (Profinite.padicIntegersRingObj ℓ E.val) d.obj.i).homEquiv _ _ e.hom ≫
            refinementRestriction (Profinite.padicIntegersRingObj ℓ E.val) r K.obj =
              (openAdjunction (Profinite.padicIntegersRingObj ℓ E.val) c.obj.i).unit.app K.obj ∧
          (φ f c d).app K = refinementIso (Profinite.padicIntegersRingObj ℓ E.val) r K.obj e)
    (localizing_pull : ∀ {X Y : Spaces k} (v : X ⟶ Y) (K : Ambient (Profinite.padicIntegersRingObj
      ℓ E.val) Y.obj.left),
    localizing (Profinite.padicIntegersRingObj ℓ E.val) Y.obj.left K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left ((pull
        (Profinite.padicIntegersRingObj ℓ E.val) v.hom.left).obj K)) :
      (∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactifications k f),
      ∃ ho : IsIso (openExchange (Profinite.padicIntegersRingObj ℓ E.val)
        (c.obj.isPullback_i_ofIsPullback sq).toCommSq),
        ∀ K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left).FullSubcategory,
          IsIso ((baseChange (Profinite.padicIntegersRingObj ℓ E.val) c.obj sq ho).app K.obj)) ∧
      (∀ {X Y X' Y' : Spaces k}
    (f : X ⟶ Y) (v : Y' ⟶ Y) (f' : X' ⟶ Y') (u' : X' ⟶ X)
    (sq : IsPullback u'.hom.left f'.hom.left f.hom.left v.hom.left)
    (c d : Compactifications k f)
    (hc : IsIso (openExchange (Profinite.padicIntegersRingObj ℓ E.val)
      (c.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange (Profinite.padicIntegersRingObj ℓ E.val)
      (d.obj.isPullback_i_ofIsPullback sq).toCommSq))
    (K : (localizing (Profinite.padicIntegersRingObj ℓ E.val) X.obj.left).FullSubcategory),
      (pull (Profinite.padicIntegersRingObj ℓ E.val) v.hom.left).map ((φ f c d).hom.app K) ≫
          (baseChange (Profinite.padicIntegersRingObj ℓ E.val) d.obj sq hd).app K.obj =
        (baseChange (Profinite.padicIntegersRingObj ℓ E.val) c.obj sq hc).app K.obj ≫
          (φ f' (baseCompactification k c sq) (baseCompactification k d sq)).hom.app
            ⟨(pull (Profinite.padicIntegersRingObj ℓ E.val) u'.hom.left).obj K.obj,
              localizing_pull u' K.obj K.property⟩) := by
  constructor
  · intro X Y X' Y' f v f' u' sq c
    have ho := cartesianOpenExchange_isIso (Profinite.padicIntegersRingObj ℓ E.val)
      (c.obj.isPullback_i_ofIsPullback sq)
    refine ⟨ho, fun K ↦ ?_⟩
    exact baseChange_isIso_of_proper (Profinite.padicIntegersRingObj ℓ E.val)
      c.obj sq ho K.obj (properExchange_on_extension k ℓ E f v f' u' sq c K)
  · exact cartesianComparisons_compatible (Profinite.padicIntegersRingObj ℓ E.val)
      k φ hc hn localizing_pull

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
