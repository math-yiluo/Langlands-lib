/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.Algebra.Homology.ExactSequence

import WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryCompletedSpecializationUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleLocalExactIndependent
import WeilConjectures.RingTheory.ProperBaseChange.BoundedWContractibleExtension
import WeilConjectures.RingTheory.ProperBaseChange.WContractibleClosedLocalization
import WeilConjectures.AlgebraicGeometry.Affine.AffineClosedSpecializationLocalization
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleAffineEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleShriekSpecializationZero
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Adjunction.Triple

/-! # The completed-coefficient module localization sequence

Source: Stacks Project, Pro-etale Cohomology, Tags 09AH, 09AG and 09BM.
(blueprint: lem-fix-ordinary-completed-localization-sequence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

private theorem ring_localization_cover {X Z : Scheme.{t}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Type t) [CommRing R] (g : Spec (CommRingCat.of R) ⟶ X) [WeaklyEtale g]
    (hR : ∀ (D : Type t) [CommRing D] (φ : R →+* D),
      φ.FaithfullyFlat → φ.WeaklyEtale → ∃ r : D →+* R, r.comp φ = RingHom.id R) :
    ∃ (n : ℕ) (V : Option (Fin n) → X.ProEt) (f : ∀ j, V j ⟶ ProEt.mk g),
      Presieve.ofArrows V f ∈ ProEt.precoverage X (ProEt.mk g) ∧
      ∀ j, (Nonempty (V j ⟶ U)) ∨
        (IsAffine (V j).left ∧
          (∀ (P Q : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) (e : P ⟶ Q),
            Epi e → Function.Surjective (e.hom.app (op (V j)))) ∧
          (∀ v : (V j).left, ∃ z : ↥(pullback (V j).hom i),
            Specializes v ((pullback.fst (V j).hom i) z))) := by
  classical
  let C : Set (PrimeSpectrum R) := g ⁻¹' Set.range i
  have hC : IsClosed C := i.isClosedEmbedding.isClosed_range.preimage g.continuous
  have hcompact : IsCompact Cᶜ := by
    have : CompactSpace ↥(pullback g U.hom) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst g U.hom)
    have hr : Cᶜ = Set.range (pullback.fst g U.hom) := by
      rw [Scheme.Pullback.range_fst]
      exact (congrArg (Set.preimage g) hU).symm
    rw [hr]
    exact isCompact_range (pullback.fst g U.hom).continuous
  obtain ⟨s, hs⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hcompact, hC.isOpen_compl⟩
  let J : Ideal R := Ideal.span (s : Set R)
  have hJ : PrimeSpectrum.zeroLocus (J : Set R) = C := by
    simpa only [J, PrimeSpectrum.zeroLocus_span, compl_compl] using
      congrArg (fun t : Set (PrimeSpectrum R) ↦ tᶜ) hs
  let e : Fin s.card ≃ s := s.equivFin.symm
  let a : Fin s.card → R := fun k ↦ (e k).val
  have ha : ∀ k, a k ∈ J := fun k ↦ Ideal.subset_span (e k).property
  have har : Set.range a = (s : Set R) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e k).property
    · intro hx
      obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hV : PrimeSpectrum.zeroLocus (J : Set R) = PrimeSpectrum.zeroLocus (Set.range a) := by
    rw [har, PrimeSpectrum.zeroLocus_span]
  let S : Submonoid R := (IsUnit.submonoid (R ⧸ J)).comap (Ideal.Quotient.mk J)
  let B := Localization S
  obtain ⟨_, _, _, hcover, hsplit⟩ :=
    IsLocalization.wcontractible_closed_localization.{t, 0} R B J s.card a ha hV
  let E := IsLocalization.closedLocalizationFamily R B a
  have hw (j : Option (Fin s.card)) : WeaklyEtale (E.f j) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hcover ⟨j⟩
  let V (j : Option (Fin s.card)) : X.ProEt :=
    have := hw j
    ProEt.mk (E.f j ≫ g)
  let f (j : Option (Fin s.card)) : V j ⟶ ProEt.mk g :=
    MorphismProperty.Over.homMk (E.f j)
  refine ⟨s.card, V, f, ?_, ?_⟩
  · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hcover
  · intro j
    cases j with
    | some k =>
      left
      have hsub : Set.range (V (some k)).hom ⊆ Set.range U.hom := by
        rintro _ ⟨x, rfl⟩
        rw [hU]
        intro hx
        have hm : PrimeSpectrum.comap (algebraMap R (Localization.Away (a k))) x ∈ C := hx
        rw [← hJ] at hm
        have hak : a k ∈
            (PrimeSpectrum.comap (algebraMap R (Localization.Away (a k))) x).asIdeal :=
          hm (ha k)
        have hn : a k ∉
            (PrimeSpectrum.comap (algebraMap R (Localization.Away (a k))) x).asIdeal := by
          have hh : PrimeSpectrum.comap (algebraMap R (Localization.Away (a k))) x ∈
              Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (a k)))) :=
            Set.mem_range_self x
          rw [PrimeSpectrum.localization_away_comap_range _ (a k)] at hh
          exact hh
        exact hn hak
      exact ⟨MorphismProperty.Over.homMk
        (IsOpenImmersion.lift U.hom (V (some k)).hom hsub)
        (IsOpenImmersion.lift_fac _ _ _)⟩
    | none =>
      right
      refine ⟨inferInstanceAs (IsAffine (Spec (.of B))), ?_, ?_⟩
      · intro P Q e he
        have := hw none
        exact ProEt.surjective_app_of_affine_ring_retractions.{t, u} X B (E.f none ≫ g)
          (hsplit hR) P Q e
      · intro v
        obtain ⟨_, _, _, _, hspec⟩ := affineClosedSpecializationLocalization R J S
          (fun _ ↦ Iff.rfl)
        obtain ⟨w, hvw, hwJ⟩ := hspec v
        have hwC : g (E.f none w) ∈ Set.range i := by
          change PrimeSpectrum.comap (algebraMap R B) w ∈ C
          rw [← hJ]
          exact hwJ
        obtain ⟨z, hz⟩ := hwC
        obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := (V none).hom) (g := i) w z hz.symm
        exact ⟨q, hq.symm ▸ hvw⟩

private theorem exists_split_affine_extension (A : Type t) [CommRing A] :
    ∃ (D : Type t) (_ : CommRing D) (φ : A →+* D),
      Presieve.singleton (Spec.map (CommRingCat.ofHom φ)) ∈
        proetalePrecoverage (Spec (CommRingCat.of A)) ∧
      (∀ (B : Type t) [CommRing B] (g : D →+* B),
        g.FaithfullyFlat → g.WeaklyEtale →
          ∃ r : B →+* D, r.comp g = RingHom.id D) := by
  obtain ⟨D, hD, φ, _, _, _, hsplit, hcover⟩ :=
    RingHom.exists_bounded_wContractible_extension.{t, 0} A
      (max Cardinal.aleph0 (Cardinal.mk A)) (le_max_left _ _) (le_max_right _ _)
  exact ⟨D, hD, φ, hcover, hsplit⟩

private theorem localization_cover {X Z : Scheme.{t}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (T : X.ProEt) :
    ∃ (I : Type (t + 1)) (V : I → X.ProEt) (f : ∀ j, V j ⟶ T),
      Presieve.ofArrows V f ∈ ProEt.precoverage X T ∧
      ∀ j, (Nonempty (V j ⟶ U)) ∨
        (IsAffine (V j).left ∧
          (∀ (P Q : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) (e : P ⟶ Q),
            Epi e → Function.Surjective (e.hom.app (op (V j)))) ∧
          (∀ v : (V j).left, ∃ z : ↥(pullback (V j).hom i),
            Specializes v ((pullback.fst (V j).hom i) z))) := by
  classical
  let A := T.left.affineOpenCover
  choose D hD φ hcover hsplit using fun j : A.I₀ ↦ exists_split_affine_extension (A.X j)
  let (j : A.I₀) : CommRing (D j) := hD j
  let p (j : A.I₀) := Spec.map (CommRingCat.ofHom (φ j))
  let C := A.openCover.weaken
    (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  let E (j : A.I₀) : Scheme.Cover.{0} proetalePrecoverage (Spec (A.X j)) :=
    .singleton (p j) (hcover j)
  let B := (C.bind E).reindex (Equiv.ulift : ULift.{t + 1} _ ≃ _)
  have hB (j : B.I₀) : WeaklyEtale (B.f j) :=
    Scheme.Cover.map_prop (Scheme.Cover.forgetQc B) j
  let W (j : B.I₀) : X.ProEt := ProEt.mk (B.f j ≫ T.hom)
  let b (j : B.I₀) : W j ⟶ T := MorphismProperty.Over.homMk (B.f j)
  have hb : Presieve.ofArrows W b ∈ ProEt.precoverage X T := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact B.mem₀
  have hlocal (j : B.I₀) :=
    ring_localization_cover.{t, u} i U hU (D j.down.1) (B.f j ≫ T.hom) (hsplit j.down.1)
  choose n V f hf hV using hlocal
  refine ⟨Σ j, Option (Fin (n j)), fun j ↦ V j.1 j.2,
    fun j ↦ f j.1 j.2 ≫ b j.1, ?_, fun j ↦ hV j.1 j.2⟩
  have : (ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [ProEt.precoverage]
    infer_instance
  exact Precoverage.comp_mem_coverings b hb f hf

private theorem module_empty_sections {X : Scheme.{t}}
    (R : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    (F : SheafOfModules.{max u (t + 1)} R) (V : X.ProEt) [IsEmpty V.left] :
    Subsingleton (F.val.obj (op V)) := by
  let G := (SheafOfModules.toSheaf R).obj F
  let T := (sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).obj G
  let : Unique (T.obj.obj (op V)) := Types.isTerminalEquivUnique _
    (T.isTerminalOfBotCover V (ProEt.bot_mem_topology V))
  change Subsingleton (T.obj.obj (op V))
  infer_instance

private theorem module_shriek_sections_subsingleton
    {X Z : Scheme.{t}} (U : X.ProEt) (i : Z ⟶ X) [IsClosedImmersion i]
    (hdisjoint : IsEmpty ↥(pullback U.hom i))
    (R : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    (G : SheafOfModules.{max u (t + 1)} (R.over U)) (V : X.ProEt) [IsAffine V.left]
    (hspec : ∀ v : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes v ((pullback.fst V.hom i) z)) :
    Subsingleton (((SheafOfModules.extensionByZeroPresheaf.{max u (t + 1)} R U ⋙
      PresheafOfModules.sheafification.{max u (t + 1)} (𝟙 R.obj)).obj G).val.obj (op V)) := by
  let P := ((SheafOfModules.extensionByZeroPresheaf.{max u (t + 1)} R U).obj G).presheaf
  let F := sheafify (ProEt.topology X) P
  let η := toSheafify (ProEt.topology X) P
  let K := (sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).obj
      ((presheafToSheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}).obj P)
  have hF : Presieve.IsSheaf (ProEt.topology X)
      (F ⋙ CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp K.property
  have hzero : ∀ s : F.obj (op V), s = 0 := by
    intro s
    obtain ⟨n, W, f, hcover, hW⟩ := ProEt.exists_specialization_cover_refinement i V
      hspec (Presheaf.imageSieve η s) (Presheaf.imageSieve_mem (ProEt.topology X) η s)
    apply (hF.isSheafFor_of_mem_precoverage hcover).isSeparatedFor.ext
    rintro T f' ⟨j⟩
    obtain ⟨p, hp⟩ := (hW j).1
    have hzP : Subsingleton (P.obj (op (W j))) := by
      have hzG (φ : W j ⟶ U) : Subsingleton (G.val.obj (op (Over.mk φ))) := by
        have hempty := ProEt.empty_of_lift_of_specializes_closed U i hdisjoint
          (W j) (hW j).2 φ.left (MorphismProperty.Over.w φ)
        let H := (SheafOfModules.toSheaf (R.over U)).obj G
        let K := (sheafCompose ((ProEt.topology X).over U)
          (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).obj H
        have hbot : (⊥ : Sieve (Over.mk φ)) ∈ (ProEt.topology X).over U (Over.mk φ) := by
          rw [GrothendieckTopology.mem_over_iff, map_bot]
          exact ProEt.bot_mem_topology (W j)
        let : Unique (K.obj.obj (op (Over.mk φ))) := Types.isTerminalEquivUnique _
          (K.isTerminalOfBotCover (Over.mk φ) hbot)
        change Subsingleton (K.obj.obj (op (Over.mk φ)))
        infer_instance
      let (φ : W j ⟶ U) : Subsingleton (G.val.obj (op (Over.mk φ))) := hzG φ
      change Subsingleton (DirectSum (W j ⟶ U)
        (fun φ ↦ G.val.obj (op (Over.mk φ))))
      infer_instance
    change F.map (f j).op s = F.map (f j).op 0
    rw [← hp, Subsingleton.elim p 0]
    simp
  refine ⟨fun s t ↦ ?_⟩
  exact (hzero s).trans (hzero t).symm

open SheafOfModules in
private theorem counit_bijective_on_open {X : AlgebraicGeometry.Scheme.{t}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) RingCat.{max u (t + 1)})
    (U : X.ProEt) [AlgebraicGeometry.IsOpenImmersion U.hom]
    (aj : (extensionByZeroPresheaf.{max u (t + 1)} R U ⋙
      PresheafOfModules.sheafification.{max u (t + 1)} (𝟙 R.obj)) ⊣ overFunctor.{max u (t + 1)} R U)
    (M : SheafOfModules.{max u (t + 1)} R) (V : X.ProEt) (φ : V ⟶ U) :
    Function.Bijective ((aj.counit.app M).val.app (op V)) := by
  let b := SheafOfModules.overPushforwardOverAdj (R := R) U
  have hsub : ∀ W : X.ProEt, Subsingleton (W ⟶ U) := by
    intro W
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).mp
    exact f.w.trans g.w.symm
  have hfull : (Over.forget U).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (@Subsingleton.elim _ (hsub V.left) _ _), rfl⟩
  let : (Over.forget U).Full := hfull
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  have : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    change IsIso (N.val.presheaf.map ((Over.forgetAdjStar U).unit.app W.unop).op)
    infer_instance
  let t : Adjunction.Triple _ _ _ := ⟨aj, b⟩
  have : IsIso aj.unit := t.isIso_unit_iff_isIso_counit.mpr inferInstance
  have : IsIso ((overFunctor R U).map (aj.counit.app M)) := by
    have htri := aj.right_triangle_components M
    have hcomp : IsIso (aj.unit.app ((overFunctor R U).obj M) ≫
        (overFunctor R U).map (aj.counit.app M)) := htri ▸ inferInstance
    exact IsIso.of_isIso_comp_left (aj.unit.app ((overFunctor R U).obj M)) _
  let E := evaluation (R.over U) (op (Over.mk φ))
  have : IsIso (E.map ((overFunctor R U).map (aj.counit.app M))) := inferInstance
  exact ConcreteCategory.bijective_of_isIso
    (E.map ((overFunctor R U).map (aj.counit.app M)))

/-- The actual slice-extension counit and completed closed-pullback unit give the
module localization sequence, with independent site and coefficient universes.

Source: Stacks Project, proetale.tex, Tags 09AH (lemma-ses-associated-to-open),
09AG (lemma-jshriek-zero), and 09BM
(lemma-closed-immersion-complement-retrocompact-exact).
(blueprint: lem-fix-ordinary-completed-localization-sequence).

Proof: use the finite-projection characterization of ordinaryCompletedRingMap
and immersion inverse-image limit preservation to identify the completed closed
coefficient map with the inverse-image coefficient isomorphism. Its module
adjunction is therefore the ringed inverse-image/direct-image adjunction.
The open term is the sheafification of the direct-sum extension presheaf, with
the counit of localizedSystemAdjunction. Refine an affine pro-etale object by
w-contractible affines. For a refined affine Spec A with closed fibre Spec A/I,
choose finitely many elements of I whose distinguished opens cover the given
quasi-compact open complement. Cover by these opens and the localization at the
elements invertible modulo I. On each open piece the extension counit is an
isomorphism and the closed direct image is zero. On the localization piece the
extension is zero, since every point specializes to the closed fibre, and the
closed unit is an isomorphism. Thus the displayed sequence is locally an identity
sequence with one zero end term. Local lifting and sheaf separation imply that
the first arrow is monic, the second epic, and image equals kernel. The scalar
actions and unit/counit identifications preserve these calculations. The same
sheafification and section arguments work in max u (t+1); no coefficient-size
identification is required. Empty pieces give the same identity sequences. -/
theorem ordinaryCompletedLocalizationSequence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Z : Scheme.{t}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsOpenImmersion V.hom] [QuasiCompact V.hom]
    (hV : Set.range V.hom = (Set.range i)ᶜ) :
    let a := SheafOfModules.localizedSystemAdjunction.{t + 1, t, u}
      (completedIntegralCommRingSheafUnrestricted l E X) V
    ∀ M : Mod l E X none,
      Mono (a.counit.app M) ∧ Epi ((ordinaryAdjunction l E i).unit.app M) ∧
      (ComposableArrows.mk₂ (a.counit.app M)
        ((ordinaryAdjunction l E i).unit.app M)).Exact := by
  dsimp only
  intro M
  let R := completedIntegralCoefficientSheafUnrestricted l E X
  let a := SheafOfModules.localizedSystemAdjunction.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) V
  have hd : IsEmpty ↥(pullback V.hom i) := by
    apply Scheme.isEmpty_pullback
    rw [hV]
    exact disjoint_compl_left
  apply proEtale_module_shortExact_of_local_sections_independent.{t, u} R (a.counit.app M)
    ((ordinaryAdjunction l E i).unit.app M)
  intro T
  obtain ⟨I, W, f, hf, hW⟩ := localization_cover.{t, u} i V hV T
  refine ⟨I, W, f, hf, ?_⟩
  intro j
  rcases hW j with hopen | ⟨hA, hw, hs⟩
  · obtain ⟨φ⟩ := hopen
    have hc := counit_bijective_on_open R V a M (W j) φ
    have hempty : IsEmpty ↥(pullback (W j).hom i) := by
      apply Scheme.isEmpty_pullback
      apply Set.disjoint_left.mpr
      rintro x ⟨w, rfl⟩ hx
      have hm : (W j).hom w ∈ Set.range V.hom := by
        refine ⟨φ.left w, ?_⟩
        exact congrArg (fun g : (W j).left ⟶ X ↦ g w)
          (MorphismProperty.Over.w φ)
      rw [hV] at hm
      exact hm hx
    have : IsEmpty ((proEtaleBaseChange i).obj (W j)).left := hempty
    have hz := module_empty_sections _ ((ordinaryPull l E i).obj M)
      ((proEtaleBaseChange i).obj (W j))
    have hz' : Subsingleton (((ordinaryPull l E i ⋙ ordinaryPush l E i).obj M).val.obj
        (op (W j))) := hz
    refine ⟨hc.1, ?_, ?_⟩
    · intro y
      exact ⟨0, @Subsingleton.elim _ hz' _ _⟩
    · intro y
      exact ⟨fun _ ↦ hc.2 y, fun _ ↦ @Subsingleton.elim _ hz' _ _⟩
  · have := hA
    have hz := module_shriek_sections_subsingleton V i hd R
      ((SheafOfModules.overFunctor R V).obj M) (W j) hs
    have hb := ordinaryCompletedSpecializationUnit l E i (W j) hw hs M
    refine ⟨fun _ _ _ ↦ @Subsingleton.elim _ hz _ _, hb.2, ?_⟩
    intro y
    constructor
    · intro hy
      refine ⟨0, ?_⟩
      rw [map_zero]
      exact hb.1 ((map_zero _).trans hy.symm)
    · rintro ⟨x, rfl⟩
      have hx : x = 0 := @Subsingleton.elim _ hz _ _
      rw [hx, map_zero, map_zero]

end WeilConjectures.IntegralOnSlice
