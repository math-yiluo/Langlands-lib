/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import all WeilConjectures.WeilSheaf.Supporting.CompletedCoefficientRingedCoherence
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Ordinary completed-coefficient module pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

private theorem chartAdjUnit {S : Scheme.{t}} (U : S.ProEt)
    (P : Sheaf (ProEt.topology S) CommRingCat.{max u (t + 1)}) (V : S.ProEtᵒᵖ) :
    ((completedRestrictionAdj.{t, u} U).unit.app P).hom.app V =
      P.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        U.hom U.prop trivial).counit.app V.unop).op := by
  simp [completedRestrictionAdj, Adjunction.sheafPushforwardContinuous,
    Adjunction.whiskerLeft]

private theorem chartConstantAdjunct {S : Scheme.{t}} (U : S.ProEt)
    (A : CommRingCat.{max u (t + 1)}) :
    (completedRestrictionAdj.{t, u} U).homEquiv _ _
        (completedRestrictConstant.{t, u} U A).hom =
      coefficientProEtaleDirectRingMap U.hom A := by
  let : HasWeakSheafify (ProEt.topology S) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} S).isRightAdjoint
  let : HasWeakSheafify (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} U.left).isRightAdjoint
  apply ((sheafificationAdjunction (ProEt.topology S)
    CommRingCat.{max u (t + 1)}).homEquiv _ _).injective
  apply NatTrans.ext
  funext V
  rw [Adjunction.homEquiv_unit]
  change (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj A)).app V ≫
      ((completedRestrictionAdj.{t, u} U).homEquiv _ _
        (completedRestrictConstant.{t, u} U A).hom).hom.app V =
    (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj A)).app V ≫
      (coefficientProEtaleDirectRingMap U.hom A).hom.app V
  rw [completedDirect_unit]
  rw [Adjunction.homEquiv_unit]
  change (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj A)).app V ≫
      ((completedRestrictionAdj.{t, u} U).unit.app
        ((constantSheaf (ProEt.topology S) CommRingCat).obj A)).hom.app V ≫
      (completedRestrictConstant.{t, u} U A).hom.hom.app
        (op ((proEtaleBaseChange U.hom).obj V.unop)) = _
  rw [chartAdjUnit]
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  change (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj A)).app V ≫
      ((constantSheaf (ProEt.topology S) CommRingCat).obj A).obj.map
        (adj.counit.app V.unop).op ≫
      (completedRestrictConstant.{t, u} U A).hom.hom.app
        (op ((proEtaleBaseChange U.hom).obj V.unop)) = _
  have hn := (toSheafify (ProEt.topology S)
    ((Functor.const S.ProEtᵒᵖ).obj A)).naturality (adj.counit.app V.unop).op
  simp only [Functor.const_obj_map] at hn
  have hn' := (Category.id_comp _).symm.trans hn
  rw [← Category.assoc]
  erw [← hn']
  exact completedRestrictConstant_unit.{t, u} U A _

private theorem chartCompletedAdjunct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S : Scheme.{t}} (U : S.ProEt) :
    (sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      ((completedRestrictionAdj.{t, u} U).homEquiv _ _
        (completedRestrictCompletion.{t, u} l E U).hom) =
      ordinaryCompletedRingMap l E U.hom := by
  let G := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  apply (ordinaryCompletedRingMap_existsUnique l E U.hom).unique
  · intro n
    have h := congrArg ((completedRestrictionAdj.{t, u} U).homEquiv _ _)
      (completedRestrictCompletion_projection.{t, u} l E U n)
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left] at h
    erw [chartConstantAdjunct] at h
    exact congrArg G.map h
  · exact (ordinaryCompletedRingMap_existsUnique l E U.hom).exists.choose_spec

private abbrev chartRestriction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S : Scheme.{t}} (U : S.ProEt) :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := completedRestrictFunctor U)
    ((sheafCompose (ProEt.topology U.left)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedRestrictCompletion.{t, u} l E U).inv)

section ModuleAdjunction
universe a b r v
variable {C D : Type a} [Category.{b} C] [Category.{b} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J]

private def commRingModuleAdjunction (adj : F ⊣ G)
    (R : Sheaf K CommRingCat.{max a b r}) (S : Sheaf J CommRingCat.{max a b r})
    (e : (F.sheafPushforwardContinuous CommRingCat.{max a b r} J K).obj R ≅ S) :
    SheafOfModules.pushforward.{v} (F := F) (J := J) (K := K)
        (R := (sheafCompose K (forget₂ CommRingCat.{max a b r} RingCat.{max a b r})).obj R)
        (S := (sheafCompose J (forget₂ CommRingCat.{max a b r} RingCat.{max a b r})).obj S)
        ((sheafCompose J (forget₂ CommRingCat.{max a b r} RingCat.{max a b r})).map e.inv) ⊣
      SheafOfModules.pushforward.{v} (F := G) (J := K) (K := J)
        (R := (sheafCompose J (forget₂ CommRingCat.{max a b r} RingCat.{max a b r})).obj S)
        (S := (sheafCompose K (forget₂ CommRingCat.{max a b r} RingCat.{max a b r})).obj R)
        ((sheafCompose K (forget₂ CommRingCat.{max a b r} RingCat.{max a b r})).map
          ((adj.sheafPushforwardContinuous (E := CommRingCat.{max a b r}) J K).homEquiv
            _ _ e.hom)) := by
  let a := adj.sheafPushforwardContinuous (E := CommRingCat.{max a b r}) J K
  apply SheafOfModules.pushforwardPushforwardAdj adj
  · have h := a.homEquiv_naturality_right e.hom e.inv
    rw [e.hom_inv_id, a.homEquiv_id] at h
    ext V x
    have hh := congrArg (fun f ↦ (f.hom.app V).hom x) h
    dsimp [sheafCompose] at *
    simpa [a, Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft,
      Functor.sheafPushforwardContinuous, CommRingCat.hom_id] using hh
  · have h := (a.homEquiv _ _).symm_apply_apply e.hom
    rw [Adjunction.homEquiv_counit] at h
    have hh := (congrArg (e.inv ≫ ·) h).trans e.inv_hom_id
    ext V x
    have hh' := congrArg (fun f ↦ (f.hom.app V).hom x) hh
    dsimp [sheafCompose] at *
    simpa [a, Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft,
      Functor.sheafPushforwardContinuous, CommRingCat.hom_id] using hh'

end ModuleAdjunction

private def chartModuleAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S : Scheme.{t}} (U : S.ProEt) :
    chartRestriction l E U ⊣ ordinaryPush l E U.hom := by
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  let a := completedRestrictionAdj.{t, u} U
  let e := completedRestrictCompletion.{t, u} l E U
  let G := sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have hc : G.map (a.homEquiv _ _ e.hom) = ordinaryCompletedRingMap l E U.hom :=
    chartCompletedAdjunct l E U
  change chartRestriction l E U ⊣ SheafOfModules.pushforward (ordinaryCompletedRingMap l E U.hom)
  rw [← hc]
  dsimp only [chartRestriction, a, completedRestrictionAdj, adj, G]
  convert! commRingModuleAdjunction.{t + 1, t, u, max u (t + 1)} adj
    (completedIntegralCommRingSheafUnrestricted l E S)
    (completedIntegralCommRingSheafUnrestricted l E U.left) e using 1
  rename_i hC hCat
  cases hC
  cases hCat
  unfold completedRestrictionAdj
  rfl

private def chartPullIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S : Scheme.{t}} (U : S.ProEt) :
    ordinaryPull l E U.hom ≅ chartRestriction l E U :=
  (ordinaryAdjunction l E U.hom).leftAdjointUniq (chartModuleAdjunction l E U)

/-- Ordinary module restriction to a pro-etale covering family detects isomorphisms.
Source: Stacks, Sites and Sheaves, Tag 04TQ; localized sites, Tag 00XZ;
Pro-etale Cohomology, Definition 09AE.
(blueprint: lem-fix-ordinary-completed-cover-detection).
Proof: a weakly etale chart identifies its pro-etale topos with the localized topos
at that chart. Finite constant-sheaf restriction is the identity on constant
sections. Slice restriction preserves limits; taking the finite-coefficient limit
therefore identifies the completed rings and every projection. Uniqueness of the
specified completed direct ring map and then uniqueness of left adjoints identify
ordinaryPull with module restriction to the chart topos. These constructions use
sheafification in module universe max u (t+1), since the sites have size t+1.
The given cover of the terminal object pulls back to a cover of each test object,
so these charts cover the top of the site. Forget module scalars to abelian sheaves.
The cover-local sheaf isomorphism criterion makes the underlying sheaf map invertible.
Its inverse is linear: apply the original linear map to the asserted scalar identity
and use its injectivity and linearity. Thus the original module map is invertible.
Empty members contribute only zero restrictions; all members together cover S.
This assertion is only about module sheaves, with no derived morphisms. -/
theorem ordinaryCompletedCoverDetection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{t}) [CompactSpace S] [QuasiSeparatedSpace S] [Nonempty S]
    (I : Type w) (W : I → S.ProEt)
    (hcompact : ∀ a : I, CompactSpace (W a).left)
    (hqs : ∀ a : I, QuasiSeparatedSpace (W a).left)
    (hcover : Presieve.ofArrows W
      (fun a ↦ (MorphismProperty.Over.homMk (W a).hom (Category.comp_id _) :
        W a ⟶ ProEt.mk (𝟙 S))) ∈ ProEt.precoverage S (ProEt.mk (𝟙 S))) :
    JointlyReflectIsomorphisms (fun a : I ↦ ordinaryPull l E (W a).hom) := by
  have _ := hcompact
  have _ := hqs
  constructor
  intro M N f hf
  have hr (a : I) : IsIso ((chartRestriction l E (W a)).map f) :=
    (NatIso.isIso_map_iff (chartPullIso l E (W a)) f).mp (hf a)
  let F := SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted l E S)
  have htop : (ProEt.topology S).CoversTop W := by
    intro V
    let q : V ⟶ ProEt.mk (𝟙 S) :=
      MorphismProperty.Over.homMk V.hom (Category.comp_id _)
    apply (ProEt.topology S).superset_covering _
      ((ProEt.topology S).pullback_stable q (Precoverage.generate_mem_toGrothendieck hcover))
    intro Z b hb
    change (Sieve.ofArrows W (fun a ↦
      (MorphismProperty.Over.homMk (W a).hom (Category.comp_id _) :
        W a ⟶ ProEt.mk (𝟙 S)))) (b ≫ q) at hb
    exact Sieve.ofArrows_le_ofObjects W _ (b ≫ q) hb
  have hlocal (a : I) (T : Over (W a)) :
      IsIso ((F.map f).hom.app (op T.left)) := by
    let := hr a
    let := ProEt.weaklyEtale_slice S (W a) T
    let V : (W a).left.ProEt := ProEt.mk T.hom.left
    have hi : IsIso (((SheafOfModules.toSheaf _).map
        ((chartRestriction l E (W a)).map f)).hom.app (op V)) := inferInstance
    change IsIso ((F.map f).hom.app
      (op ((completedRestrictFunctor (W a)).obj V))) at hi
    let e : (completedRestrictFunctor (W a)).obj V ≅ T.left :=
      MorphismProperty.Over.isoMk (Iso.refl _) (by
        change (𝟙 T.left.left) ≫ T.left.hom = T.hom.left ≫ (W a).hom
        simpa only [Category.id_comp] using (MorphismProperty.Over.w T.hom).symm)
    exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ (F.map f).hom _ _ e.op hi
  have : IsIso (F.map f) := by
    apply Sheaf.isIso_of_coversTop htop
    intro a
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro T
    exact hlocal a T.unop
  exact isIso_of_reflects_iso f F

end WeilConjectures.IntegralOnSlice
