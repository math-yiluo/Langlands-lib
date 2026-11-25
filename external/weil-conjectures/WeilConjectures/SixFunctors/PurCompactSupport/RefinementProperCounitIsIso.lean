/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestrictionData
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedClopenComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedRestrictionExchangeOpenDescent
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCompactified
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece

/-! Isomorphism of the proper counit after restriction to the distinguished open. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor proEtaleRingDerivedAdjunction refinementPull

attribute [local instance 100000] proEtaleRingModules_hasDerivedCategory
  SheafOfModules.instAbelian

-- Complete the missing coefficient comparison without any coherence assumption on R.
private theorem completeCoefficientIso {I : Sort*} {C : Type*} [Category C]
    (F : I → C) {i k : I} (h : i = k) {A B : C}
    (e : F i ≅ B) (p : F k ≅ A) :
    ∃ c : A ≅ B, HEq e (p ≪≫ c) := by
  subst k
  exact ⟨p.symm ≪≫ e, by simp⟩

private theorem pullTriangle {A B C : Scheme.{u}} (h : C ⟶ B) (g : B ⟶ A)
    (k : C ⟶ A) (hk : k = h ≫ g)
    (RA : Sheaf (ProEt.topology A) CommRingCat.{u + 1})
    (RB : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (RC : Sheaf (ProEt.topology C) CommRingCat.{u + 1})
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RA ≅ RB)
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RA ≅ RC) :
    ∃ ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RB ≅ RC,
      Nonempty (proEtaleRingDerivedPullback k RA RC ck ≅
        proEtaleRingDerivedPullback g RA RB cg ⋙ proEtaleRingDerivedPullback h RB RC ch) := by
  subst k
  let ch := ((proEtaleRingInverseImageComp h g).app RA ≪≫
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso cg).symm ≪≫ ck
  have he : proEtaleRingCompositeCoefficients h g RA RB RC cg ch = ck := by
    simp [ch, proEtaleRingCompositeCoefficients]
  exact ⟨ch, ⟨eqToIso (congrArg (proEtaleRingDerivedPullback (h ≫ g) RA RC) he.symm) ≪≫
    proEtaleCanonicalPullbackComposition h g RA RB RC cg ch⟩⟩

attribute [-instance] SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall in
private theorem derivedOpenUnit {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj RV ≅ RU) :
    IsIso (proEtaleRingDerivedOpenAdjunction j RV RU c).unit := by
  obtain ⟨e, ⟨he⟩⟩ := proEtaleOpen_slicePresentation j RV RU c
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let he' := Functor.mapDerivedCategoryNatIso he ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  let L := (SheafOfModules.localizedModuleExtension.{u} RV (ProEt.mk j)).mapDerivedCategory
  let adjL := SheafOfModules.localizedModuleDerivedAdjunction.{u} RV (ProEt.mk j)
  have : IsIso adjL.unit := SheafOfModules.localizedDerivedUnit_isIso j RV
  have : L.Full := adjL.fullyFaithfulLOfIsIsoUnit.full
  have : L.Faithful := adjL.fullyFaithfulLOfIsIsoUnit.faithful
  have : (proEtaleRingDerivedOpenExtension j RV RU c).Full := Functor.Full.of_iso he'.symm
  have : (proEtaleRingDerivedOpenExtension j RV RU c).Faithful :=
    Functor.Faithful.of_iso he'.symm
  exact (proEtaleRingDerivedOpenAdjunction j RV RU c).unit_isIso_of_L_fully_faithful

-- Identity scheme pullback is an equivalence for every coefficient identification.
private theorem identityPullEquivalence
    (W : Scheme.{u}) (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage (𝟙 W) CommRingCat.{u + 1}).obj R ≅ R) :
    (proEtaleRingDerivedPullback (𝟙 W) R R c).IsEquivalence := by
  let a := proEtaleSheafAdjunction (𝟙 W) CommRingCat.{u + 1}
  let : IsIso a.unit :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0}
      (𝟙 W) CommRingCat.{u + 1}).2.1
  let : IsIso (proEtaleRingDirectImageMap (𝟙 W) R R c) := by
    unfold proEtaleRingDirectImageMap
    infer_instance
  let ρ := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap (𝟙 W) R R c)
  have hρ : IsIso ρ := by dsimp only [ρ]; infer_instance
  let e := @isoModulePushforwardEquivalence W W (𝟙 W) (inferInstance)
    ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ρ hρ
  let : (proEtaleRingModuleDirectImage (𝟙 W) R R c).IsEquivalence :=
    inferInstanceAs e.functor.IsEquivalence
  let : (proEtaleRingModulePullback (𝟙 W) R R c).IsEquivalence :=
    (proEtaleRingModuleAdjunction (𝟙 W) R R c).isEquivalence_left_of_isEquivalence_right
  infer_instance

private theorem pullEquivalenceOfEqId (W : Scheme.{u}) (t : W ⟶ W) (ht : t = 𝟙 W)
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage t CommRingCat.{u + 1}).obj R ≅ R) :
    (proEtaleRingDerivedPullback t R R c).IsEquivalence := by
  subst t
  exact identityPullEquivalence W R c

private theorem sectionCounit
    {C A : Type*} [Category C] [Category A]
    {F : C ⥤ A} {P : A ⥤ C} {V : A ⥤ C} {J : C ⥤ A}
    (a : F ⊣ P) (b : V ⊣ J) (K : C)
    [(F ⋙ V).IsEquivalence] [J.Full] [J.Faithful] :
    IsIso (V.map (a.counit.app (J.obj K))) := by
  have : IsIso (a.comp b).counit := inferInstance
  have : IsIso (V.map (a.counit.app (J.obj K)) ≫ b.counit.app K) := by
    simpa only [Adjunction.comp_counit_app] using
      (inferInstance : IsIso ((a.comp b).counit.app K))
  exact IsIso.of_isIso_comp_right _ (b.counit.app K)

-- Keep the mate calculation abstract to avoid unfolding the concrete derived categories.
private theorem restrictionCounit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {P : B ⥤ A} {F' : C ⥤ D} {P' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} {V : D ⥤ C}
    {J : C ⥤ D} {L : D ⥤ B} {K : C ⥤ B} {U : B ⥤ C}
    (a : F ⊣ P) (b : F' ⊣ P') (al : L ⊣ H) (aj : J ⊣ V) (ak : K ⊣ U)
    (rev : V ⊣ J) (k : U ≅ H ⋙ V) (θ : G ⋙ F' ≅ F ⋙ H)
    [IsIso al.unit] [IsIso aj.unit] [(F' ⋙ V).IsEquivalence]
    [IsIso (mateEquiv a b (TwoSquare.mk _ _ _ _ θ.hom))] (M : C) :
    IsIso (U.map (a.counit.app (K.obj M))) := by
  have : J.Full := aj.fullyFaithfulLOfIsIsoUnit.full
  have : J.Faithful := aj.fullyFaithfulLOfIsIsoUnit.faithful
  let ec : K ≅ J ⋙ L := ak.leftAdjointUniq ((aj.comp al).ofNatIsoRight k.symm)
  let N := K.obj M
  let eN : H.obj N ≅ J.obj M :=
    H.mapIso (ec.app M) ≪≫ (asIso (al.unit.app (J.obj M))).symm
  have hs : IsIso (V.map (b.counit.app (J.obj M))) := sectionCounit b rev M
  have hN : IsIso (V.map (b.counit.app (H.obj N))) :=
    (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight b.counit V) eN).mpr hs
  let β := (mateEquiv a b (TwoSquare.mk _ _ _ _ θ.hom))
  have hm := mateEquiv_counit a b (TwoSquare.mk _ _ _ _ θ.hom) N
  have hh : IsIso (V.map (θ.hom.app _) ≫ V.map (H.map (a.counit.app N))) := by
    rw [← Functor.map_comp, ← hm, Functor.map_comp]
    change IsIso (V.map (F'.map (β.app N)) ≫ V.map (b.counit.app (H.obj N)))
    infer_instance
  have hi : IsIso (V.map (H.map (a.counit.app N))) :=
    IsIso.of_isIso_comp_left (V.map (θ.hom.app _)) _
  exact (NatIso.isIso_map_iff k (a.counit.app N)).mpr hi

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleRingOpenExtension proEtaleRingDerivedOpenAdjunction
  proEtaleCanonicalPullbackComposition proEtaleAmbientRingedPullbackComparison

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/--
Source: Stacks 0F7B and 0F7I, clopen distinguished-section calculation.
The proper counit becomes invertible after pulling back along the distinguished
open immersion because the refinement fibre product decomposes into that clopen
section and its complement; extension by zero has zero restriction to the
complement and the counit is invertible on the section.
(blueprint: lem-sf-refinement-open-restriction-proper-counit-is-iso).
-/
theorem refinementProperCounit_isIso
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    IsIso ((pull R c.i).map ((proEtaleRingDerivedAdjunction r.hom
      (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app
      ((openExtension R c.i).mapDerivedCategory.obj M))) := by
  let g := pullback.fst r.hom d.i
  let p := pullback.snd r.hom d.i
  let s : X ⟶ pullback r.hom d.i :=
    pullback.lift c.i (𝟙 X) (by simpa using r.i_hom)
  have hsg : s ≫ g = c.i := pullback.lift_fst _ _ _
  have hsp : s ≫ p = 𝟙 X := pullback.lift_snd _ _ _
  have : IsOpenImmersion (s ≫ g) := hsg ▸ inferInstance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s g
  have : IsClosedImmersion (s ≫ p) := hsp ▸ inferInstance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s p
  -- Use the actual inverse-image ring, then complete the two coefficient triangles.
  let RW := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (R.ring c.Z)
  obtain ⟨cs, ⟨k⟩⟩ := pullTriangle s g c.i hsg.symm
    (R.ring c.Z) RW (R.ring X) (Iso.refl _) (R.pull c.i)
  let sq := RingedRestrictionExchange.cartesian r.hom d.i
  obtain ⟨cp, hcp⟩ := completeCoefficientIso
    (fun q : pullback r.hom d.i ⟶ d.Z ↦
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj (R.ring d.Z))
    (pullback.condition (f := r.hom) (g := d.i))
    (proEtaleRingCompositeCoefficients g r.hom (R.ring d.Z) (R.ring c.Z) RW
      (R.pull r.hom) (Iso.refl _))
    ((proEtaleRingInverseImageComp p d.i).app (R.ring d.Z) ≪≫
      (proEtaleSheafInverseImage p CommRingCat.{u + 1}).mapIso (R.pull d.i))
  let q : StrictTowerRingedSquare sq :=
    { RY := R.ring d.Z, RX := R.ring c.Z, RY' := R.ring X, RX' := RW
      cf := R.pull r.hom, cg := R.pull d.i, cg' := Iso.refl _, cf' := cp
      coherent := by
        simpa only [proEtaleRingCompositeCoefficients, Iso.trans_assoc] using hcp }
  let Us := proEtaleRingDerivedPullback s RW (R.ring X) cs
  let Up := proEtaleRingDerivedPullback p (R.ring X) RW cp
  let Js := proEtaleRingDerivedOpenExtension s RW (R.ring X) cs
  let ag := proEtaleRingDerivedOpenAdjunction g (R.ring c.Z) RW (Iso.refl _)
  let ac := openDerivedAdjunction R c.i
  let aS := proEtaleRingDerivedOpenAdjunction s RW (R.ring X) cs
  let ar := proEtaleRingDerivedAdjunction r.hom (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)
  let ap := proEtaleRingDerivedAdjunction p (R.ring X) RW cp
  -- The clopen section has the reverse adjunction as well as the open adjunction.
  obtain ⟨bs⟩ := WeilConjectures.IntegralSystemRealization.ordinaryClopenReverse
    s RW (R.ring X) cs
  let bS : Us ⊣ Js := bs.mapExactDerivedCategory
  have : IsIso ag.unit := derivedOpenUnit g (R.ring c.Z) RW (Iso.refl _)
  have : IsIso aS.unit := derivedOpenUnit s RW (R.ring X) cs
  let ci := proEtaleRingCompositeCoefficients s p (R.ring X) RW (R.ring X) cp cs
  let e := proEtaleCanonicalPullbackComposition s p (R.ring X) RW (R.ring X) cp cs
  have : (Up ⋙ Us).IsEquivalence := by
    have he : (proEtaleRingDerivedPullback (s ≫ p) (R.ring X) (R.ring X) ci).IsEquivalence := by
      exact pullEquivalenceOfEqId X (s ≫ p) hsp (R.ring X) ci
    exact Functor.isEquivalence_of_iso e
  have hβ : IsIso (RingedRestrictionExchange.exchange q) :=
    (RingedRestrictionExchange.open_comparison q).2
  change IsIso ((mateEquiv ar ap
    (TwoSquare.mk _ _ _ _ (RingedRestrictionExchange.pullSquare q).hom))) at hβ
  exact restrictionCounit ar ap ag aS ac bS k (RingedRestrictionExchange.pullSquare q) M

/--
Source: the definition of `refinementRestriction` in the coefficient comparison
construction, with the pullback compositor of Tags 03D8 and 0D6D.
The specified component is exactly the compositor followed by the pulled-back
proper counit; this is the formal factorization used to reduce the component
isomorphism to the geometric counit calculation.
(blueprint: lem-sf-refinement-open-restriction-factorization).
-/
theorem refinementRestriction_factorization
    (M : DerivedCategory (pbcModules X (R.ring X))) :
    refinementRestriction R r hi M =
      (refinementPull R r hi).hom.app
          ((push R r.hom).obj ((openExtension R c.i).mapDerivedCategory.obj M)) ≫
        (pull R c.i).map ((proEtaleRingDerivedAdjunction r.hom
          (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit.app
          ((openExtension R c.i).mapDerivedCategory.obj M)) := by
  -- Normalize the transported open triangle before applying the defining equation.
  revert hi
  rcases c with ⟨Zc, gc, ic, hc, hpc, hoc⟩
  rcases d with ⟨Zd, gd, jd, hd, hpd, hod⟩
  rcases r with ⟨v, hv, hvg⟩
  change Zc ⟶ Zd at v
  change ic ≫ v = jd at hv
  change v ≫ gd = gc at hvg
  subst jd
  intro hi
  let c : Compactification f := ⟨Zc, gc, ic, hc, hpc, hoc⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ v, hd, hpd, hod⟩
  let r : c.Refinement d := ⟨v, rfl, hvg⟩
  exact refinementRestriction.eq_def R r hi M

end WeilConjectures.PurCompactSupport
